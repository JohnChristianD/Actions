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
  , ("walsh-hadamard", ["walshHadamardApply", "walshOrthonormal", "walshNormPreservation"])
  , ("recurrent-nonlinearity", ["quadraticActivation", "hardSign", "gruInputSeparation", "gruParametersPersistent"])
  , ("canonical-gru-composition", ["canonicalGRUStep", "canonicalPersistentGRUPreservation"])
  , ("optimizer", ["F4IntUState", "F4IntUKernel", "f4ThetaStep", "f4ParameterInvariant"])
  , ("whole-step", ["canonicalFullStep", "canonicalFullStep-clock", "canonicalFullStep-critic", "canonicalFullStep-attention", "canonicalFullStep-gru", "canonicalFullStep-optimizer", "canonicalFullStep-counts", "canonicalFullStep-qLog"])
  ]

legacyTokens :: [String]
legacyTokens =
  [ "signReLU"
  , "softsign"
  , "haarApply"
  , "haarRow0"
  , "haarRow1"
  , "helmertApply"
  , "SharedActorCritic"
  , "SparsemaxActorVsCriticTheorem"
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

findLegacyTokens :: FilePath -> IO [(String, FilePath)]
findLegacyTokens path = do
  source <- readFile path
  pure
    [ (token, path)
    | token <- legacyTokens
    , token `isInfixOf` source
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
  legacy <- fmap concat (mapM findLegacyTokens relativeFiles)
  let duplicates =
        [ (family, symbol, sort [path | (defined, path) <- definitions, defined == symbol, path /= canonical])
        | (family, symbols) <- canonicalSymbols
        , symbol <- symbols
        , let paths = [path | (defined, path) <- definitions, defined == symbol, path /= canonical]
        , not (null paths)
        ]
      legacyActive =
        [ (token, path)
        | (token, path) <- legacy
        , path `notElem` retiredPaths
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
    else mapM_ reportDuplicate duplicates

  putStrLn "legacy-surface-audit="
  if null legacyActive
    then putStrLn "  clean"
    else mapM_ reportLegacy legacyActive

  putStrLn "retirement-policy=report-only-until-owner-is-confirmed"
  if null retiredPresent && null duplicates && null legacyActive then exitSuccess else exitFailure
  where
    reportDuplicate (family, symbol, paths) =
      putStrLn ("  DUPLICATE " ++ family ++ ":" ++ symbol ++ " -> " ++ show paths)
    reportLegacy (token, path) =
      putStrLn ("  LEGACY_ACTIVE " ++ token ++ " -> " ++ path)
