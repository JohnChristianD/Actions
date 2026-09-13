module Main where

import Data.List (intercalate)
import System.Exit (ExitCode(..), exitFailure, exitSuccess)
import System.Process (readProcessWithExitCode)

data Method = Method
  { name :: String
  , moduleName :: String
  , stateName :: String
  , stepName :: String
  , irreducibilityName :: String
  , selfLoopName :: String
  }

methods :: [Method]
methods =
  [ Method
      "MR15"
      "Exotic.ERL.Exploration.MR15Reachability"
      "MR15State"
      "MR15Step"
      "mr15IrreducibilityProof"
      "mr15SelfLoopProof"
  , Method
      "OpenES"
      "Exotic.ERL.Exploration.OpenESDyadic"
      "OpenESState"
      "openESStep"
      "openESIrreducibilityProof"
      "openESSelfLoopProof"
  , Method
      "NoisyNet"
      "Exotic.ERL.FullCoupled.NoisyNetCoupled"
      "CoupledNoisyNetState"
      "NoisyNetStep"
      "noisyNetIrreducibilityProof"
      "noisyNetSelfLoopProof"
  ]

generatedPath :: FilePath
generatedPath = "Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda"

renderCandidate :: String
renderCandidate = unlines $
  [ "{-# OPTIONS --safe #-}"
  , "module Exotic.ERL.Exploration.Generated.ExplorationCandidates where"
  , ""
  , "-- Generated proof harness. Haskell only constructs this source; Agda --safe accepts it or rejects it."
  , "open import Exotic.ERL.Exploration.ExplorationTheoremSchema using"
  , "  ( Irreducible"
  , "  ; SelfLoop"
  , "  ; PeriodOne"
  , "  ; periodOne-from-components"
  , "  )"
  ]
  ++ concatMap renderMethod methods
  where
    renderMethod m =
      [ ""
      , "open import " ++ moduleName m
      , ""
      , name m ++ "KernelIrreducibility : Irreducible " ++ stepName m
      , name m ++ "KernelIrreducibility = " ++ irreducibilityName m
      , ""
      , name m ++ "KernelSelfLoop : SelfLoop " ++ stepName m
      , name m ++ "KernelSelfLoop = " ++ selfLoopName m
      , ""
      , name m ++ "KernelPeriodOne : PeriodOne " ++ stepName m
      , name m ++ "KernelPeriodOne = periodOne-from-components "
          ++ name m ++ "KernelIrreducibility " ++ name m ++ "KernelSelfLoop"
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
  if null output then pure () else putStrLn output
  case code of
    ExitSuccess -> exitSuccess
    ExitFailure _ -> exitFailure
  where
    squash = intercalate " " . words
