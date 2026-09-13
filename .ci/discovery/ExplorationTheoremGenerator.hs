module Main where

import Data.List (intercalate, isInfixOf)
import System.Exit (ExitCode(..), exitFailure, exitSuccess)
import System.Process (readProcessWithExitCode)

record :: String -> String -> [String] -> (String, String, [String])
record name path proofs = (name, path, proofs)

methods :: [(String, String, [String])]
methods =
  [ record "MR15" "Exotic/ERL/Exploration/MR15Reachability.agda"
      ["mr15Irreducible", "mr15SelfLoop"]
  , record "OpenES" "Exotic/ERL/Exploration/OpenESDyadic.agda"
      ["openESIrreducible", "openESSelfLoop"]
  , record "NoisyNet" "Exotic/ERL/FullCoupled/NoisyNetCoupled.agda"
      ["noisyNetIrreducible", "noisyNetSelfLoop"]
  ]

data Status = Proven | MissingProof | AgdaFailure deriving (Eq, Show)

checkMethod :: (String, String, [String]) -> IO (String, Status, [String])
checkMethod (name, path, required) = do
  source <- readFile path
  let missing = filter (\symbol -> not (symbol `isInfixOf` source)) required
  if not (null missing)
    then pure (name, MissingProof, missing)
    else do
      (code, _out, err) <- readProcessWithExitCode "agda" ["--safe", path] ""
      case code of
        ExitSuccess -> pure (name, Proven, [])
        ExitFailure _ -> pure (name, AgdaFailure, [err])

renderCandidateModule :: [(String, Status, [String])] -> String
renderCandidateModule results =
  unlines $
    [ "{-# OPTIONS --safe #-}"
    , "module Exotic.ERL.Exploration.Generated.ExplorationCandidates where"
    , ""
    , "-- Generated theorem-discovery report. Agda remains the acceptance oracle."
    , ""
    ]
    ++ concatMap render results
  where
    render (name, status, details) =
      [ "-- method: " ++ name
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
  if any (\(_, status, _) -> status == AgdaFailure) results
    then exitFailure
    else exitSuccess
  where
    printResult (name, status, details) =
      putStrLn $
        "exploration-method=" ++ name
        ++ ",status=" ++ show status
        ++ if null details then "" else ",details=" ++ intercalate ";" details
