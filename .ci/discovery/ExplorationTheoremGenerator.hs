module Main where

import Data.List (intercalate, isInfixOf)
import System.Exit (ExitCode(..), exitFailure, exitSuccess)
import System.Process (readProcessWithExitCode)

laws :: [(String, String)]
laws = [("Flat", "flatDyadic")]

methods :: [(String, String, String, [String])]
methods =
  [ ("MR15", "Exotic/ERL/Exploration/MR15Reachability.agda", "mr15GA"
    , ["mr15IrreducibilityProof", "mr15SelfLoopProof", "mr15PeriodOneProof"])
  , ("OpenES", "Exotic/ERL/Exploration/OpenESDyadic.agda", "openES"
    , ["openESIrreducibilityProof", "openESSelfLoopProof", "openESPeriodOneProof"])
  , ("NoisyNet", "Exotic/ERL/FullCoupled/NoisyNetCoupled.agda", "noisyNetGRU"
    , ["noisyNetGRUIrreducible", "noisyNetGRUSelfLoop", "noisyNetGRUPeriodOne", "noisyNetProjectionLift"])
  ]

data Status = Proven | MissingProof | AgdaFailure deriving (Eq, Show)

checkMethod :: (String, String, String, [String]) -> IO (String, Status, [String])
checkMethod (name, path, _methodTag, required) = do
  source <- readFile path
  let missing = filter (\symbol -> not (symbol `isInfixOf` source)) required
  if not (null missing)
    then pure (name, MissingProof, missing)
    else do
      (code, _out, err) <- readProcessWithExitCode "agda" ["--safe", path] ""
      case code of
        ExitSuccess -> pure (name, Proven, [])
        ExitFailure _ -> pure (name, AgdaFailure, [err])

renderCandidateModule :: [(String, String, String, Status, [String])] -> String
renderCandidateModule results =
  unlines $
    [ "{-# OPTIONS --safe #-}"
    , "module Exotic.ERL.Exploration.Generated.ExplorationCandidates where"
    , ""
    , "open import Agda.Builtin.Nat using (Nat)"
    , ""
    , "-- Generated flat-dyadic theorem-discovery report."
    , "-- Agda remains the only acceptance oracle."
    , ""
    ]
    ++ concatMap render results
    ++ [ "flatDyadicLawMethodPermutationCount : Nat"
       , "flatDyadicLawMethodPermutationCount = 3"
       ]
  where
    render (lawName, lawTag, methodName, status, details) =
      [ "-- law: " ++ lawName ++ " (" ++ lawTag ++ ")"
      , "-- method: " ++ methodName
      , "-- status: " ++ show status
      , "-- details: " ++ intercalate " | " details
      , ""
      ]

main :: IO ()
main = do
  methodResults <- mapM checkMethod methods
  let results =
        [ (lawName, lawTag, methodName, status, details)
        | (lawName, lawTag) <- laws
        , (methodName, _path, _methodTag, _required) <- methods
        , let (status, details) =
                case lookupMethod methodName methodResults of
                  Nothing -> (AgdaFailure, ["missing method result"])
                  Just (s, d) -> (s, d)
        ]
  writeFile "Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda"
    (renderCandidateModule results)
  mapM_ printResult results
  if any (\(_, _, _, status, _) -> status /= Proven) results
    then exitFailure
    else exitSuccess
  where
    lookupMethod _ [] = Nothing
    lookupMethod name ((n, status, details) : rest)
      | name == n = Just (status, details)
      | otherwise = lookupMethod name rest

    printResult (lawName, _lawTag, methodName, status, details) =
      putStrLn $
        "law=" ++ lawName
        ++ ",method=" ++ methodName
        ++ ",status=" ++ show status
        ++ if null details then "" else ",details=" ++ intercalate ";" details
