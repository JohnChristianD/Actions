module Main where

import Data.List (intercalate)
import System.Exit (ExitCode(..), exitFailure, exitSuccess)
import System.Process (readProcessWithExitCode)

methods :: [(String, String)]
methods =
  [ ("GRUOpenES", "gruOpenES")
  , ("GRUMR15", "gruMR15")
  , ("GRUNoisyNet", "gruNoisyNet")
  ]

generatedPath :: FilePath
generatedPath = "Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda"

renderCandidate :: String
renderCandidate = unlines $
  [ "{-# OPTIONS --safe #-}"
  , "module Exotic.ERL.Exploration.Generated.ExplorationCandidates where"
  , ""
  , "-- Generated GRU exploration theorem harness. Haskell constructs source;"
  , "-- Agda --safe is the acceptance oracle."
  , "open import Exotic.ERL.Exploration.DyadicLaw using"
  , "  ( flatDyadicNormalized; flatDyadicUnitSupport )"
  , "open import Exotic.ERL.Exploration.FlatDyadicEligibility using"
  , "  ( flatDyadicAllFiniteEligibility )"
  , "open import Exotic.ERL.Exploration.GRUPerturbationMethods using"
  , "  ( GRUPerturbationMethod"
  , "  ; GRUStep"
  , "  ; gruAperiodic"
  , "  )"
  , ""
  , "FlatDyadicEligibility = flatDyadicAllFiniteEligibility"
  , "FlatDyadicNormalized = flatDyadicNormalized"
  , "FlatDyadicUnitSupport = flatDyadicUnitSupport"
  ]
  ++ concatMap renderMethod methods
  where
    renderMethod (label, ctor) =
      [ ""
      , label ++ "Aperiodic = gruAperiodic " ++ ctor
      , label ++ "Step = GRUStep " ++ ctor
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
  putStrLn $ "gru-method-count=" ++ show (length methods)
  putStrLn "exploration-theorem-class=GRU-OpenES,GRU-MR15,GRU-NoisyNet"
  putStrLn "strict-method-order=requires-explicit-projection-lift-retraction"
  putStrLn "law-frontier=FlatDyadic"
  putStrLn "aperiodicity=irreducible-plus-self-loop"
  if null output then pure () else putStrLn output
  case code of
    ExitSuccess -> exitSuccess
    ExitFailure _ -> exitFailure
  where
    squash = intercalate " " . words
