module Main where

import Data.List (intercalate)
import System.Exit (ExitCode(..), exitFailure, exitSuccess)
import System.Process (readProcessWithExitCode)

data Method = Method
  { name :: String
  , moduleName :: String
  , stepName :: String
  , irreducibilityName :: String
  , selfLoopName :: String
  }

methods :: [Method]
methods =
  [ Method
      "MR15"
      "Exotic.ERL.Exploration.MR15Reachability"
      "MR15Step"
      "mr15IrreducibilityProof"
      "mr15SelfLoopProof"
  , Method
      "OpenES"
      "Exotic.ERL.Exploration.OpenESDyadic"
      "openESStep"
      "openESIrreducibilityProof"
      "openESSelfLoopProof"
  , Method
      "NoisyNet"
      "Exotic.ERL.FullCoupled.NoisyNetCoupled"
      "NoisyNetStep"
      "noisyNetIrreducibilityProof"
      "noisyNetSelfLoopProof"
  ]

data Law = Law
  { lawName :: String
  , lawCtor :: String
  , normalizationName :: String
  , supportName :: String
  }

-- Probability laws parameterize actual exploration methods. They are not
-- exploration methods themselves. The legacy triangular law is intentionally
-- absent from this finite theorem enumeration.
laws :: [Law]
laws =
  [ Law "LazyWalk" "lazyWalk" "lazyWalkNormalized" "law-unit-support lazyWalk"
  , Law "DyadicLadder" "dyadicLadder" "dyadicLadderNormalized" "law-unit-support dyadicLadder"
  , Law "FlatDyadic" "flatDyadic" "flatDyadicNormalized" "law-unit-support flatDyadic"
  ]

generatedPath :: FilePath
generatedPath = "Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda"

renderCandidate :: String
renderCandidate = unlines $
  [ "{-# OPTIONS --safe #-}"
  , "module Exotic.ERL.Exploration.Generated.ExplorationCandidates where"
  , ""
  , "-- Generated method × probability-law proof harness."
  , "-- Haskell only constructs this source; Agda --safe is the acceptance oracle."
  , "open import Exotic.ERL.Exploration.DyadicLaw using"
  , "  ( DyadicLaw"
  , "  ; lazyWalk"
  , "  ; dyadicLadder"
  , "  ; flatDyadic"
  , "  ; law-unit-support"
  , "  )"
  , "open import Exotic.ERL.FullCoupled.FullAlgebraicCoupling using"
  , "  ( FullAlgebraicCoupling"
  , "  ; composeFull"
  , "  )"
  ]
  ++ concatMap renderMethod methods
  where
    renderMethod m =
      [ ""
      , "open import " ++ moduleName m
      ]
      ++ concatMap (renderPermutation m) laws

    renderPermutation m l =
      [ ""
      , name m ++ lawName l ++ "Endogenous : FullAlgebraicCoupling "
          ++ lawCtor l ++ " " ++ stepName m
      , name m ++ lawName l ++ "Endogenous = composeFull "
          ++ lawCtor l ++ " " ++ normalizationName l ++ " "
          ++ supportName l ++ " "
          ++ irreducibilityName m ++ " " ++ selfLoopName m
      , ""
      ]

runKernelCheck :: IO (ExitCode, String)
runKernelCheck = do
  (code, out, err) <- readProcessWithExitCode "agda" ["--safe", generatedPath] ""
  pure (code, out ++ err)

main :: IO ()
main = do
  writeFile generatedPath renderCandidate
  (code, output) <- runKernelCheck
  let status = case code of
        ExitSuccess -> "PASS"
        ExitFailure _ -> "FAIL"
      summary = unlines
        [ "-- generator-status: " ++ status
        , "-- generator-check-output: " ++ squash output
        , ""
        , renderCandidate
        ]
  writeFile generatedPath summary
  putStrLn $ "exploration-theorem-generator=" ++ status
  putStrLn $ "exploration-law-method-permutations=" ++ show (length methods * length laws)
  if null output then pure () else putStrLn output
  case code of
    ExitSuccess -> exitSuccess
    ExitFailure _ -> exitFailure
  where
    squash = intercalate " " . words
