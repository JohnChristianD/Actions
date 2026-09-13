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
  , strong :: Bool
  }

methods :: [Method]
methods =
  [ Method "MR15" "Exotic.ERL.Exploration.MR15Reachability" "MR15Step"
      "mr15IrreducibilityProof" "mr15SelfLoopProof" False
  , Method "OpenES" "Exotic.ERL.Exploration.OpenESDyadic" "openESStep"
      "openESIrreducibilityProof" "openESSelfLoopProof" False
  , Method "NoisyNet" "Exotic.ERL.FullCoupled.NoisyNetCoupled" "NoisyNetStep"
      "noisyNetIrreducibilityProof" "noisyNetSelfLoopProof" True
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
  , Law "FlatDyadic" "flatDyadic" "flatDyadicNormalized" "flatDyadicUnitSupport"
  ]

generatedPath :: FilePath
generatedPath = "Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda"

renderCandidate :: String
renderCandidate = unlines $
  [ "{-# OPTIONS --safe #-}"
  , "module Exotic.ERL.Exploration.Generated.ExplorationCandidates where"
  , ""
  , "-- Generated method × law full-composition theorem harness."
  , "-- Haskell constructs source; Agda --safe is the acceptance oracle."
  , "open import Exotic.ERL.Exploration.DyadicLaw using"
  , "  ( DyadicLaw; lazyWalk; lazyWalkNormalized; lazyWalkUnitSupport"
  , "  ; dyadicLadder; dyadicLadderNormalized; dyadicLadderUnitSupport"
  , "  ; flatDyadic; flatDyadicNormalized; flatDyadicUnitSupport"
  , "  )"
  , "open import Exotic.ERL.FullCoupled.FullAlgebraicCoupling using"
  , "  ( FullAlgebraicCoupling; composeFull )"
  , "open import Exotic.ERL.FullCoupled.TheoremStrengthV2 using"
  , "  ( StrongEndogenous; strongEndogenous )"
  , "open import Exotic.ERL.FullCoupled.SoftsignGatedRepresentation using"
  , "  ( SoftsignGatedRepresentation; SoftsignGatedStep; noisyNetSoftsignFactor )"
  , "open import Exotic.efficient_chad.SoftsignGatedComposition using"
  , "  ( softsignGatedForwardLaw-proof; softsignGatedPullbackLaw-proof )"
  ]
  ++ concatMap renderMethod methods
  where
    renderMethod m =
      [ "", "open import " ++ moduleName m ]
      ++ concatMap (renderPermutation m) laws

    renderPermutation m l =
      [ ""
      , name m ++ lawName l ++ "Full : FullAlgebraicCoupling "
          ++ lawCtor l ++ " " ++ stepName m
      , name m ++ lawName l ++ "Full = composeFull "
          ++ lawCtor l ++ " " ++ normalizationName l ++ " "
          ++ unitSupportName l ++ " "
          ++ "softsignGatedForwardLaw-proof softsignGatedPullbackLaw-proof "
          ++ irreducibilityName m ++ " " ++ selfLoopName m
      ]
      ++ if strong m
           then
             [ name m ++ lawName l ++ "Theorem : "
                 ++ "StrongEndogenous {S = CoupledNoisyNetState} {R = SoftsignGatedRepresentation} "
                 ++ lawCtor l ++ " " ++ stepName m ++ " SoftsignGatedStep"
             , name m ++ lawName l ++ "Theorem = strongEndogenous "
                 ++ name m ++ lawName l ++ "Full noisyNetSoftsignFactor"
             ]
           else
             [ name m ++ lawName l ++ "Theorem : FullAlgebraicCoupling "
                 ++ lawCtor l ++ " " ++ stepName m
             , name m ++ lawName l ++ "Theorem = "
                 ++ name m ++ lawName l ++ "Full"
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
