module Main where

import Data.List (isInfixOf, sort)
import System.Directory (doesDirectoryExist, doesFileExist, getCurrentDirectory, listDirectory)
import System.Exit (exitFailure, exitSuccess)
import System.FilePath (takeExtension, (</>))

canonical :: FilePath
canonical = "Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda"

retiredPaths :: [FilePath]
retiredPaths =
  [ "Exotic/ERL/Exploration/MR15Reachability.agda"
  , "Exotic/ERL/Exploration/OpenESDyadic.agda"
  , "Exotic/ERL/FullCoupled/NoisyNetCoupled.agda"
  , "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicBehavior.agda"
  , "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicBehavior_test.agda"
  , "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicSeparation.agda"
  , "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicSeparation_test.agda"
  , "Exotic/ERL/FullCoupled/SharedActorCritic.agda"
  , "Exotic/ERL/FullCoupled/SparsemaxActorVsCriticTheorem.agda"
  , "Exotic/ERL/FullCoupled/SparsemaxActorVsCriticTheorem_test.agda"
  , "Exotic/econlib/RockPaperScissors.agda"
  , "Exotic/econlib/RockPaperScissors_test.agda"
  ]

canonicalSymbols :: [(String, [String])]
canonicalSymbols =
  [ ("q-log", ["finiteQLog8", "negativeFiniteQLog8", "negativeAlpha8", "canonicalQLogControl", "qLogSignal", "canonicalQLogStep"])
  , ("action-selection", ["temperatureScaledSparsemax", "scheduledActionScore", "canonicalPolicy", "updateLCBCount"])
  , ("learned-attention", ["LearnedSparsemaxAttention", "learnedSparsemaxAttentionWeights", "canonicalAttentionStep"])
  , ("haar", ["haarApply", "haarRow0", "haarRow1", "dot2"])
  , ("canonical-gru-composition", ["canonicalGRUStep", "canonicalPersistentGRUPreservation"])
  , ("optimizer", ["F4IntUState", "F4IntUKernel", "f4ThetaStep", "f4ParameterInvariant"])
  , ("whole-step", ["canonicalFullStep", "canonicalFullStep-clock", "canonicalFullStep-critic", "canonicalFullStep-attention", "canonicalFullStep-gru", "canonicalFullStep-optimizer", "canonicalFullStep-counts", "canonicalFullStep-qLog"])
  ]

normalize :: String -> String
normalize = unwords

isDefinitionOf :: String -> String -> Bool
isDefinitionOf symbol line =
  let text = normalize line
  in (symbol ++ " :") `isInfixOf` text || (symbol ++ " =") `isInfixOf` text

agdaFiles :: FilePath -> IO [FilePath]
agdaFiles dir = do
  names <- listDirectory dir
  fmap concat (mapM visit names)
  where
    visit name = do
      let path = dir </> name
      isDir <- doesDirectoryExist path
      if isDir
        then if name == ".git" || (dir == ".ci" && name == "external")
             then pure []
             else agdaFiles path
        else pure [path | takeExtension path == ".agda"]

relativeTo :: FilePath -> FilePath -> FilePath
relativeTo root path =
  let prefix = root ++ "/"
  in if prefix `isInfixOf` path then drop (length prefix) path else path

findDefinitions :: FilePath -> IO [(String, FilePath)]
findDefinitions path = do
  source <- readFile path
  pure
    [ (symbol, path)
    | (_, symbols) <- canonicalSymbols
    , symbol <- symbols
    , any (isDefinitionOf symbol) (lines source)
    ]

ownerAllowed :: FilePath -> Bool
ownerAllowed path =
  path == canonical
    || path == "Exotic/ERL/FullCoupled/SparsemaxCriticWatkins.agda"
    || path == "Exotic/ERL/FullCoupled/DyadicGRU.agda"
    || path == "Exotic/ERL/FullCoupled/FrozenOrthogonalAttentionGRU.agda"
    || path == "Exotic/ERL/FullCoupled/MobiusGroup.agda"
    || path == "Exotic/ERL/FullCoupled/Int8StabilityComposition.agda"

main :: IO ()
main = do
  root <- getCurrentDirectory
  exists <- doesFileExist (root </> canonical)
  if not exists
    then putStrLn ("ERROR: canonical learner missing: " ++ canonical) >> exitFailure
    else pure ()

  files <- agdaFiles root
  let relativeFiles = sort (map (relativeTo root) files)
      retiredPresent = filter (`elem` relativeFiles) retiredPaths
      ownerFiles = filter ownerAllowed relativeFiles

  definitions <- fmap concat (mapM findDefinitions ownerFiles)
  let duplicates =
        [ (family, symbol, sort [path | (defined, path) <- definitions, defined == symbol, path /= canonical])
        | (family, symbols) <- canonicalSymbols
        , symbol <- symbols
        , let paths = [path | (defined, path) <- definitions, defined == symbol, path /= canonical]
        , not (null paths)
        ]

  putStrLn ("canonical-learner=" ++ canonical)
  putStrLn ("agda-files-scanned=" ++ show (length relativeFiles))
  putStrLn "retired-path-audit="
  if null retiredPresent
    then putStrLn "  clean"
    else mapM_ (putStrLn . ("  RETIRED_PRESENT " ++)) retiredPresent

  putStrLn "canonical-owned-duplicate-audit="
  if null duplicates
    then putStrLn "  clean"
    else mapM_ report duplicates

  putStrLn "retirement-policy=report-only-until-owner-is-confirmed"
  if null retiredPresent && null duplicates then exitSuccess else exitFailure
  where
    report (family, symbol, paths) =
      putStrLn ("  DUPLICATE " ++ family ++ ":" ++ symbol ++ " -> " ++ show paths)
