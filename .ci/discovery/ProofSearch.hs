{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Exception (SomeException, try)
import Control.Monad (forM, forM_, when)
import Data.List (foldl', minimumBy, nub, sortBy)
import Data.Ord (comparing)
import System.Directory
  ( createDirectoryIfMissing
  , doesFileExist
  , getCurrentDirectory
  , removePathForcibly
  , writeFile
  )
import System.Environment (getArgs)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)


data Candidate = Candidate
  { actions :: [String]
  }
  deriving (Eq, Show)


data Goal = Goal
  { goalName :: String
  , goalStatement :: String
  , proofMacros :: [(String, String)]
  }
  deriving (Eq, Show)


data SearchBackend
  = Auto
  | Mcts
  | Mr15Ga
  | AStar
  deriving (Eq, Show)


goals :: [Goal]
goals =
  [ Goal
      "clock-lower-bound-search"
      "∀ {A} (K : L.LearnerKernel A) n s r → L.clock s ≤ L.clock (L.iterateLearner K n s r)"
      [("clock-lower-bound", "T.clock-lower-bound K n s r")]
  , Goal
      "score-sort-permutation-search"
      "∀ {A} (q : L.QVec A) (c : L.CountVec A) → Sort.sort (L.scoreEntryOrder A) (L.scoreList q c) ↭ L.scoreList q c"
      [("sort-permutation", "T.scoreList-sort-permutation q c")]
  , Goal
      "score-sort-sorted-search"
      "∀ {A} (q : L.QVec A) (c : L.CountVec A) → Sorted (Sort.sort (L.scoreEntryOrder A) (L.scoreList q c))"
      [("sort-sorted", "T.scoreList-sort-sorted q c")]
  ]


lookupProof :: Goal -> Candidate -> Maybe String
lookupProof goal (Candidate [action]) = lookup action (proofMacros goal)
lookupProof _ _ = Nothing

renderModule :: Goal -> Candidate -> FilePath -> String
renderModule goal candidate moduleName =
  case lookupProof goal candidate of
    Nothing -> ""
    Just proof ->
      unlines
        [ "{-# OPTIONS --safe #-}"
        , "module " ++ moduleName ++ " where"
        , ""
        , "open import Data.Fin using (Fin)"
        , "open import Data.List.Sort as Sort"
        , "open import Data.List.Relation.Unary.Sorted.TotalOrder using (Sorted)"
        , "open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)"
        , "open import Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith as T"
        , "open Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L"
        , ""
        , goalName goal ++ " : " ++ goalStatement goal
        , goalName goal ++ " = " ++ proof
        ]


proofSearchRoot :: FilePath -> FilePath
proofSearchRoot root = root </> ".ci" </> ".proof-search-tmp"


kernelCheck :: FilePath -> FilePath -> IO Bool
kernelCheck root path = do
  result <- try (readProcessWithExitCode "agda" ["--safe", path] "") :: IO (Either SomeException (ExitCode, String, String))
  pure $ case result of
    Right (ExitSuccess, _, _) -> True
    _ -> False


writeCandidate :: FilePath -> Goal -> Candidate -> IO (Maybe FilePath)
writeCandidate root goal candidate =
  case lookupProof goal candidate of
    Nothing -> pure Nothing
    Just _ -> do
      let moduleName = "GeneratedSearch_" ++ map hyphenToUnderscore (goalName goal)
          dir = proofSearchRoot root
          path = dir </> moduleName ++ ".agda"
      createDirectoryIfMissing True dir
      writeFile path (renderModule goal candidate moduleName)
      pure (Just path)
  where
    hyphenToUnderscore '-' = '_'
    hyphenToUnderscore c = c


candidateOK :: FilePath -> Goal -> Candidate -> IO Bool
candidateOK root goal candidate = do
  maybePath <- writeCandidate root goal candidate
  case maybePath of
    Nothing -> pure False
    Just path -> kernelCheck root path


verifySurface :: FilePath -> FilePath -> IO ()
verifySurface root relativePath = do
  let path = root </> relativePath
  result <- try (readProcessWithExitCode "agda" ["--safe", path] "") :: IO (Either SomeException (ExitCode, String, String))
  case result of
    Right (ExitSuccess, _, _) -> pure ()
    Right (_, stdoutText, stderrText) -> do
      putStrLn stdoutText
      putStrLn stderrText
      error ("kernel surface failed: " ++ relativePath)
    Left err -> error ("could not invoke agda for " ++ relativePath ++ ": " ++ show err)


verifySurfaces :: FilePath -> IO ()
verifySurfaces root = do
  verifySurface root "Exotic/ERL/FullCoupled/GeneralFullCoupledLearnerMonolith.agda"
  verifySurface root "Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremsMonolith.agda"


-- MCTS-style stage: UCT selection over the proof macro grammar, followed by
-- an unconditional Agda kernel check. The grammar is intentionally typed and
-- finite today; the tree is the hook for deeper proof-state expansion later.
mctsSearch :: FilePath -> Goal -> Int -> IO (Maybe Candidate)
mctsSearch root goal budget = do
  let actions0 = map fst (proofMacros goal)
      initial = [(action, 0 :: Int, 0 :: Int) | action <- actions0]
  run initial 0
  where
    run _ simulations | simulations >= budget = pure Nothing
    run stats simulations = do
      let totalVisits = max 1 (sum [v | (_, v, _) <- stats])
          score (_, visits, wins)
            | visits == 0 = 1 / 0
            | otherwise = fromIntegral wins / fromIntegral visits + sqrt (2 * log (fromIntegral totalVisits) / fromIntegral visits)
          (chosenAction, _, _) = minimumBy (comparing (negate . score)) stats
          candidate = Candidate [chosenAction]
      ok <- candidateOK root goal candidate
      let stats' = map (update chosenAction ok) stats
      if ok
        then pure (Just candidate)
        else run stats' (simulations + 1)
    update action ok item@(name, visits, wins)
      | name /= action = item
      | ok = (name, visits + 1, wins + 1)
      | otherwise = (name, visits + 1, wins)


-- MR15-GA-style stage: deterministic population, elitist selection, and
-- multi-point mutation of discrete proof-macro indices. RandomSearch is not
-- present: every generation is derived from the selected population.
mr15gaSearch :: FilePath -> Goal -> Int -> IO (Maybe Candidate)
mr15gaSearch root goal budget = do
  let actions0 = map fst (proofMacros goal)
      n = length actions0
      populationSize = max 2 (min 16 budget)
  if n == 0
    then pure Nothing
    else evolve populationSize 0 (seedPopulation n populationSize) actions0
  where
    evolve _ evaluations _ _ | evaluations >= budget = pure Nothing
    evolve popSize evaluations population actions0 = do
      checked <- forM population $ \index -> do
        let candidate = Candidate [actions0 !! normalizeIndex index (length actions0)]
        ok <- candidateOK root goal candidate
        pure (index, candidate, ok)
      case [candidate | (_, candidate, True) <- checked] of
        candidate : _ -> pure (Just candidate)
        [] -> do
          let ranked = sortBy (comparing fitness) checked
              elites = take (max 1 (popSize `div` 4)) [index | (index, _, _) <- ranked]
              nextPopulation = take popSize (elites ++ concatMap (mutateFrom n) elites)
          evolve popSize (evaluations + popSize) nextPopulation actions0

    fitness (index, _, _) = abs index

    mutateFrom n index =
      [ normalizeIndex (index + 1) n
      , normalizeIndex (index + 2) n
      , normalizeIndex (index * 3 + 1) n
      , normalizeIndex (index * 5 + 2) n
      ]

seedPopulation :: Int -> Int -> [Int]
seedPopulation n populationSize = take populationSize (0 : concat [[i, i + 1] | i <- [1 .. max 1 n]])

normalizeIndex :: Int -> Int -> Int
normalizeIndex x n
  | n <= 0 = 0
  | otherwise = x `mod` n


-- A* stage: bounded exact best-first exploration of the same finite grammar.
aStarSearch :: FilePath -> Goal -> Int -> IO (Maybe Candidate)
aStarSearch root goal budget = search [Candidate []] [] 0
  where
    actions0 = map fst (proofMacros goal)

    search [] _ _ = pure Nothing
    search _ _ expansions | expansions >= budget = pure Nothing
    search (candidate : queue) seen expansions
      | actions candidate `elem` seen = search queue seen expansions
      | otherwise = do
          ok <- candidateOK root goal candidate
          if ok
            then pure (Just candidate)
            else
              let seen' = actions candidate : seen
                  children =
                    if null (actions candidate)
                      then [Candidate [a] | a <- actions0]
                      else []
                  queue' = sortBy (comparing cost) (queue ++ children)
              in search queue' seen' (expansions + 1)

    cost (Candidate xs) = length xs


searchGoal :: FilePath -> Goal -> Int -> SearchBackend -> IO (Maybe Candidate)
searchGoal root goal budget backend = case backend of
  AStar -> aStarSearch root goal budget
  Mcts -> do
    primary <- mctsSearch root goal budget
    maybe (aStarSearch root goal budget) (pure . Just) primary
  Mr15Ga -> do
    primary <- mr15gaSearch root goal budget
    maybe (aStarSearch root goal budget) (pure . Just) primary
  Auto -> do
    primary <- mctsSearch root goal budget
    case primary of
      Just candidate -> pure (Just candidate)
      Nothing -> do
        secondary <- mr15gaSearch root goal budget
        maybe (aStarSearch root goal budget) (pure . Just) secondary


jsonEscape :: String -> String
jsonEscape = concatMap escape
  where
    escape '"' = "\\\""
    escape '\\' = "\\\\"
    escape '\n' = "\\n"
    escape '\r' = "\\r"
    escape '\t' = "\\t"
    escape c = [c]


renderResults :: [(String, String, String)] -> String
renderResults rows =
  unlines $
    [ "{" ]
    ++ [ "  \"" ++ jsonEscape name ++ "\": {\"proof\": \"" ++ jsonEscape proof ++ "\", \"status\": \"kernel-checked\"}" ++ comma i
       | (i, (name, proof, _)) <- zip [0 :: Int ..] rows
       ]
    ++ [ "}" ]
  where
    comma i
      | i + 1 == length rows = ""
      | otherwise = ","


parseBackend :: String -> SearchBackend
parseBackend value = case value of
  "mcts" -> Mcts
  "mr15-ga" -> Mr15Ga
  "astar" -> AStar
  _ -> Auto

parseArgs :: [String] -> (SearchBackend, Int)
parseArgs args =
  let backend = case dropWhile (/= "--backend") args of
        _ : value : _ -> parseBackend value
        _ -> Auto
      budget = case dropWhile (/= "--budget") args of
        _ : value : _ -> case reads value of
          (n, _) : _ -> max 1 n
          _ -> 24
        _ -> 24
  in (backend, budget)


main :: IO ()
main = do
  args <- getArgs
  root <- getCurrentDirectory
  let (backend, budget) = parseArgs args
      output = root </> "Exotic/ERL/Exploration/Generated/ExplorationCandidates.json"
      tmp = proofSearchRoot root
  verifySurfaces root
  rows <- forM goals $ \goal -> do
    result <- searchGoal root goal budget backend
    case result of
      Nothing -> error ("no kernel-checked proof candidate for " ++ goalName goal)
      Just candidate -> do
        let proofName = case actions candidate of
              action : _ -> action
              [] -> ""
        putStrLn ("goal=" ++ goalName goal ++ " backend=" ++ show backend ++ " status=kernel-checked proof=" ++ proofName)
        pure (goalName goal, proofName, "kernel-checked")
  createDirectoryIfMissing True (root </> "Exotic/ERL/Exploration/Generated")
  writeFile output (renderResults rows)
  exists <- doesFileExist output
  when exists (putStrLn "kernel-oracle=agda --safe")
  cleanupResult <- try (removePathForcibly tmp) :: IO (Either SomeException ())
  case cleanupResult of
    Left _ -> pure ()
    Right _ -> pure ()
