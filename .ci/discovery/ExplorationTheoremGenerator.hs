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
  [ Method "MR15" "Exotic.ERL.Exploration.MR15Reachability" "MR15Step"
      "mr15IrreducibilityProof" "mr15SelfLoopProof"
  , Method "OpenES" "Exotic.ERL.Exploration.OpenESDyadic" "openESStep"
      "openESIrreducibilityProof" "openESSelfLoopProof"
  , Method "NoisyNet" "Exotic.ERL.FullCoupled.NoisyNetCoupled" "NoisyNetStep"
      "noisyNetIrreducibilityProof" "noisyNetSelfLoopProof"
  ]

data Law = Law
  { lawName :: String
  , lawCtor :: String
  , normalizationName :: String
  , unitSupportName :: String
  }

laws :: [Law]
laws =
  [ Law "LazyWalk" "lazyWalk" "lazyWalkNormalized" "lazyWalkUnitSupport"
  , Law "DyadicLadder" "dyadicLadder" "dyadicLadderNormalized" "dyadicLadderUnitSupport"
  , Law "DyadicGeometric5" "dyadicGeometric5" "dyadicGeometric5Normalized" "dyadicGeometric5UnitSupport"
  ]

generatedPath :: FilePath
generatedPath = "Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda"

renderCandidate :: String
renderCandidate = unlines $
  [ "{-# OPTIONS --safe #-}"
  , "module Exotic.ERL.Exploration.Generated.ExplorationCandidates where"
  , ""
  , "-- Generated law × method full-composition theorem harness."
  , "-- Haskell constructs source; Agda --safe is the acceptance oracle."
  , "open import Exotic.ERL.Exploration.DyadicLaw using"
  , "  ( DyadicLaw; lazyWalk; lazyWalkNormalized; lazyWalkUnitSupport"
  , "  ; dyadicLadder; dyadicLadderNormalized; dyadicLadderUnitSupport"
  , "  ; dyadicGeometric5; dyadicGeometric5Normalized; dyadicGeometric5UnitSupport"
  , "  )"
  , "open import Exotic.ERL.FullCoupled.FullAlgebraicCoupling using"
  , "  ( FullAlgebraicCoupling; composeFull )"
  , "open import Exotic.efficient_chad.SoftsignGatedComposition using"
  , "  ( softsignGatedForwardLaw-proof; softsignGatedPullbackLaw-proof )"
  , "open import Exotic.ERL.FullCoupled.TheoremStrengthV3 using"
  , "  ( openESPeriodOneFromMR15; mr15PeriodOneFromNoisyNet"
  , "  ; openES-lt-MR15; MR15-lt-NoisyNet )"
  ]
  ++ concatMap renderMethod methods
  ++ [ ""
     , "StrictOpenESLTMR15 = openES-lt-MR15"
     , "StrictMR15LTNoisyNet = MR15-lt-NoisyNet"
     ]
  where
    renderMethod m =
      [ "", "open import " ++ moduleName m ]
      ++ concatMap (renderPermutation m) laws

    renderPermutation m l =
      [ ""
      , name m ++ lawName l ++ "Endogenous : FullAlgebraicCoupling "
          ++ lawCtor l ++ " " ++ stepName m
      , name m ++ lawName l ++ "Endogenous = composeFull "
          ++ lawCtor l ++ " " ++ normalizationName l ++ " "
          ++ unitSupportName l ++ " "
          ++ "softsignGatedForwardLaw-proof softsignGatedPullbackLaw-proof "
          ++ irreducibilityName m ++ " " ++ selfLoopName m
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
  putStrLn "exploration-theorem-order=OpenES<MR15<NoisyNet"
  if null output then pure () else putStrLn output
  case code of
    ExitSuccess -> exitSuccess
    ExitFailure _ -> exitFailure
  where
    squash = intercalate " " . words
