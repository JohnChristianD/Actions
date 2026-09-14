module Main where

import Data.List (intercalate, isInfixOf)
import System.Exit (ExitCode(..), exitFailure, exitSuccess)
import System.Process (readProcessWithExitCode)

data Candidate = Candidate
  { candidateName :: String
  , candidatePath :: String
  , requiredProofs :: [String]
  }

methods :: [Candidate]
methods =
  [ Candidate "MR15" "Exotic/ERL/Exploration/MR15Reachability.agda"
      ["mr15IrreducibilityProof", "mr15SelfLoopProof"]
  , Candidate "OpenES" "Exotic/ERL/Exploration/OpenESDyadic.agda"
      ["openESIrreducibilityProof", "openESSelfLoopProof"]
  , Candidate "NoisyNet-GRU" "Exotic/ERL/FullCoupled/NoisyNetCoupled.agda"
      ["noisyNetIrreducibilityProof", "noisyNetSelfLoopProof"]
  , Candidate "GRU-coupling" "Exotic/ERL/FullCoupled/GRUCoupled.agda"
      ["coupledReachability", "coupledSelfLoop", "coupledPeriodOne"]
  ]

laws :: [String]
laws = ["FlatDyadic"]

data Status = Proven | MissingProof | AgdaFailure deriving (Eq, Show)

data Result = Result String String Status [String]

checkCandidate :: Candidate -> IO (String, Status, [String])
checkCandidate c = do
  source <- readFile (candidatePath c)
  let missing = filter (\symbol -> not (symbol `isInfixOf` source)) (requiredProofs c)
  if not (null missing)
    then pure (candidateName c, MissingProof, missing)
    else do
      (code, _out, err) <- readProcessWithExitCode "agda" ["--safe", candidatePath c] ""
      case code of
        ExitSuccess -> pure (candidateName c, Proven, [])
        ExitFailure _ -> pure (candidateName c, AgdaFailure, [err])

permutations :: [(String, String)]
permutations = [(candidateName m, l) | m <- methods, l <- laws]

renderCandidateModule :: [(String, Status, [String])] -> String
renderCandidateModule results =
  unlines $
    [ "{-# OPTIONS --safe #-}"
    , "module Exotic.ERL.Exploration.Generated.ExplorationCandidates where"
    , ""
    , "-- Generated finite theorem-discovery survivor report."
    , "-- Each law-method permutation is a candidate; Agda --safe is the acceptance oracle."
    , "-- No statistical or environment-dependent ordering is inferred."
    , ""
    ]
    ++ concatMap renderPermutation permutations
    ++ concatMap renderResult results
  where
    renderPermutation (methodName, lawName) =
      [ "-- candidate: " ++ methodName ++ " x " ++ lawName
      ]
    renderResult (name, status, details) =
      [ "-- checked: " ++ name
      , "-- status: " ++ show status
      , "-- details: " ++ intercalate " | " details
      , ""
      ]

main :: IO ()
main = do
  results <- mapM checkCandidate methods
  writeFile "Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda"
    (renderCandidateModule results)
  mapM_ printResult results
  if any (\(_, status, _) -> status /= Proven) results
    then exitFailure
    else exitSuccess
  where
    printResult (name, status, details) =
      putStrLn $
        "exploration-candidate=" ++ name
        ++ ",status=" ++ show status
        ++ if null details then "" else ",details=" ++ intercalate ";" details
