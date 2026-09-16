module Main where

import Data.List (intercalate, isInfixOf)
import System.Exit (ExitCode(..), exitFailure, exitSuccess)
import System.Process (readProcessWithExitCode)

canonicalPath :: String
canonicalPath = "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda"

proofs :: [String]
proofs =
  [ "temperatureCodeLaw"
  , "temperatureTieLaw"
  , "temperaturePositiveUnitLaw"
  , "temperatureNegativeUnitLaw"
  , "negativeFiniteQLogLaw"
  , "hardGate-state-independent"
  , "walshOrthonormal"
  , "mobiusAssociativity"
  , "persistent-preservation"
  , "gruParameterPersistence"
  , "gruActivationBoundary"
  , "canonicalPersistentGRUPreservation"
  , "canonicalRecurrentInput-law"
  , "canonicalPolicy-attention-invariant"
  , "f4ParameterInvariant"
  , "pessimisticInit"
  , "pessimisticCritic-law"
  , "canonicalFullStep-clock"
  , "canonicalFullStep-watkins"
  , "canonicalFullStep-attention"
  , "canonicalFullStep-gru"
  , "canonicalFullStep-optimizer"
  , "canonicalFullStep-counts"
  , "canonicalFullStep-qLog"
  , "canonicalFullStep-qLogControl"
  , "canonicalStep-not-fixed"
  , "canonicalTotalCountStep"
  , "canonicalAperiodic"
  , "canonicalOrbitNonFixed"
  , "canonicalNoNontrivialFiniteCycle"
  , "canonicalNoCountedTwoCycle"
  ]

data Status = Proven | MissingProof | AgdaFailure deriving (Eq, Show)

checkCanonical :: IO (Status, [String])
checkCanonical = do
  source <- readFile canonicalPath
  let missing = filter (\symbol -> not (symbol `isInfixOf` source)) proofs
  if not (null missing)
    then pure (MissingProof, missing)
    else do
      (code, out, err) <- readProcessWithExitCode "agda" ["--safe", canonicalPath] ""
      case code of
        ExitSuccess -> pure (Proven, [])
        ExitFailure _ -> pure (AgdaFailure, [err ++ out])

render :: Status -> [String] -> String
render status details = unlines $
  [ "{-# OPTIONS --safe #-}"
  , "module Exotic.ERL.Exploration.Generated.ExplorationCandidates where"
  , ""
  , "-- Generated status for the single canonical learner monolith."
  , "-- This report is descriptive only; Agda proof terms remain authoritative."
  , ""
  , "-- theorem-family: CanonicalLearnerMonolith"
  , "-- status: " ++ show status
  , "-- details: " ++ intercalate " | " details
  , ""
  ]

main :: IO ()
main = do
  (status, details) <- checkCanonical
  writeFile "Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda" (render status details)
  putStrLn ("theorem-family=CanonicalLearnerMonolith,status=" ++ show status)
  if status == Proven then exitSuccess else exitFailure
