module Main where

import Data.List (intercalate, isInfixOf)
import System.Exit (ExitCode(..), exitFailure, exitSuccess)
import System.Process (readProcessWithExitCode)

record :: String -> String -> [String] -> (String, String, [String])
record name path proofs = (name, path, proofs)

methods :: [(String, String, [String])]
methods =
  [ record "CanonicalLearner" "Exotic/ERL/FullCoupled/CanonicalSparsemaxLearner.agda"
      [ "temperatureCodeLaw"
      , "temperatureTieLaw"
      , "temperaturePositiveUnitLaw"
      , "temperatureNegativeUnitLaw"
      , "negativeFiniteQLogLaw"
      , "haar00"
      , "haar11"
      , "haar01"
      , "canonicalFullStep-clock"
      , "canonicalFullStep-critic"
      , "canonicalFullStep-gru"
      , "canonicalFullStep-optimizer"
      , "canonicalFullStep-attention"
      , "canonicalFullStep-counts"
      , "canonicalFullStep-qLog"
      , "canonicalQuadraticDecay"
      , "canonicalAperiodic"
      , "canonicalCoerciveNoCycle"
      ]
  ]

data Status = Proven | MissingProof | AgdaFailure deriving (Eq, Show)

checkMethod :: (String, String, [String]) -> IO (String, Status, [String])
checkMethod (name, path, required) = do
  source <- readFile path
  let missing = filter (\symbol -> not (symbol `isInfixOf` source)) required
  if not (null missing)
    then pure (name, MissingProof, missing)
    else do
      (code, out, err) <- readProcessWithExitCode "agda" ["--safe", path] ""
      case code of
        ExitSuccess -> pure (name, Proven, [])
        ExitFailure _ -> pure (name, AgdaFailure, [err ++ out])

renderCandidateModule :: [(String, Status, [String])] -> String
renderCandidateModule results =
  unlines $
    [ "{-# OPTIONS --safe #-}"
    , "module Exotic.ERL.Exploration.Generated.ExplorationCandidates where"
    , ""
    , "-- Generated theorem-status report for the canonical endogenous learner."
    , "-- Agda remains the acceptance oracle; generation never upgrades missing proof terms."
    , ""
    ]
    ++ concatMap render results
  where
    render (name, status, details) =
      [ "-- theorem-family: " ++ name
      , "-- status: " ++ show status
      , "-- details: " ++ intercalate " | " details
      , ""
      ]

main :: IO ()
main = do
  results <- mapM checkMethod methods
  writeFile "Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda"
    (renderCandidateModule results)
  mapM_ printResult results
  if any (\(_, status, _) -> status /= Proven) results
    then exitFailure
    else exitSuccess
  where
    printResult (name, status, details) =
      putStrLn $
        "theorem-family=" ++ name
        ++ ",status=" ++ show status
        ++ if null details then "" else ",details=" ++ intercalate ";" details
