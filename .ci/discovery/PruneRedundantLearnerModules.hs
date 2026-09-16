module Main where

import Control.Monad (forM_)
import Data.List (isInfixOf, sort)
import System.Directory (doesFileExist, listDirectory)
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import System.FilePath ((</>))
import System.Process (callProcess)

canonical :: FilePath
canonical = "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda"

candidates :: [FilePath]
candidates =
  [ "Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda"
  , "Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2_test.agda"
  , "Exotic/ERL/FullCoupled/SparsemaxCriticWatkins.agda"
  , "Exotic/ERL/FullCoupled/SparsemaxCriticWatkins_test.agda"
  , "Exotic/ERL/FullCoupled/DyadicGRU.agda"
  , "Exotic/ERL/FullCoupled/MobiusRational.agda"
  , "Exotic/ERL/FullCoupled/MobiusGroup.agda"
  , "Exotic/ERL/FullCoupled/FrozenOrthonormalWalshGRU.agda"
  , "Exotic/ERL/FullCoupled/Int8StabilityComposition.agda"
  , "Exotic/ERL/FullCoupled/MobiusSemidirectCycleComposition.agda"
  , "Exotic/ERL/FullCoupled/FiniteSemidirectComposition.agda"
  , "Exotic/ERL/FullCoupled/GRUCompositionAlgebra.agda"
  , "Exotic/ERL/FullCoupled/CountMemoryCycleTheorem.agda"
  , "Exotic/ERL/FullCoupled/CountMemoryCycleTheorem_test.agda"
  , "Exotic/ERL/FullCoupled/AllSafeCombined.agda"
  , "Exotic/ERL/FullCoupled/AllSafeCombined_test.agda"
  , "Exotic/ERL/FullCoupled/DeterministicQSA.agda"
  , "Exotic/ERL/FullCoupled/DeterministicQSA_test.agda"
  ]

moduleName :: FilePath -> String
moduleName p = map slashToDot (stripAgda p)
  where
  stripAgda q = if ".agda" `isInfixOf` q then take (length q - 5) q else q
  slashToDot '/' = '.'
  slashToDot c = c

allTextFiles :: FilePath -> IO [FilePath]
allTextFiles dir = do
  entries <- listDirectory dir
  fmap concat $ mapM visit entries
  where
  visit name = do
    let path = dir </> name
    if name == ".git" || (dir == ".ci" && name == "external")
      then pure []
      else do
        exists <- doesFileExist path
        if exists
          then pure [path]
          else pure []

containsImport :: String -> String -> Bool
containsImport modName txt =
  any (matches . words) (lines txt)
  where
  matches ws =
    case ws of
      ("import" : m : _) -> m == modName
      ("open" : "import" : m : _) -> m == modName
      _ -> False

usersOf :: String -> IO [FilePath]
usersOf modName = do
  files <- allTextFiles "."
  hits <- fmap concat $ mapM (inspect modName) files
  pure (sort hits)
  where
  inspect m p = do
    txt <- readFile p
    pure [p | p /= canonical && p /= "./" ++ canonical && containsImport m txt]

prunable :: FilePath -> IO Bool
prunable path = do
  users <- usersOf (moduleName path)
  putStrLn $ "candidate=" ++ path ++ ",module=" ++ moduleName path ++ ",users=" ++ show users
  pure (null users)

main :: IO ()
main = do
  args <- getArgs
  let apply = "--apply" `elem` args
  exists <- doesFileExist canonical
  if not exists
    then putStrLn ("missing canonical learner: " ++ canonical) >> exitFailure
    else do
      decisions <- mapM (\p -> (,) p <$> prunable p) candidates
      let safe = [p | (p, ok) <- decisions, ok]
      putStrLn ("canonical=" ++ canonical)
      putStrLn ("prunable=" ++ show safe)
      if apply
        then do
          forM_ safe $ \p -> do
            existsP <- doesFileExist p
            if existsP then callProcess "git" ["rm", "-q", p] else pure ()
          putStrLn "prune-mode=applied"
          exitSuccess
        else do
          putStrLn "prune-mode=dry-run"
          putStrLn "pass --apply to delete only candidates with zero repository-local import users"
          if null safe then exitSuccess else exitSuccess
