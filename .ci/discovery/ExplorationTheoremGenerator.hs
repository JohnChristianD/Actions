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

ablations :: [(String, String)]
ablations =
  [ ("NoisyNet-GRU", "noisyNetGRUAblation")
  , ("NoisyNet-Sparsemax-only", "noisyNetSparsemaxOnlyAblation")
  , ("NoisyNet-Sparsemax+GRU", "noisyNetSparsemaxAndGRUAblation")
  , ("MR15-flat", "mr15Ablation")
  , ("OpenES-flat", "openESAblation")
  ]

chadReferences :: [(String, String, String)]
chadReferences =
  [ ("CHAD", "original combinatory homomorphic automatic differentiation line"
    , "semantic AD correctness and compositionality discovery reference")
  , ("Efficient CHAD", "tomsmeding/efficient-chad-agda"
    , "efficiency-oriented implementation and cost-model specification reference")
  , ("Iterative CHAD", "iterative CHAD / recursive-iteration extension literature"
    , "iteration and recursion discovery reference")
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

checkAblationFile :: IO (Status, [String])
checkAblationFile = do
  let path = "Exotic/ERL/FullCoupled/FlatDyadicExplorationAblations.agda"
      required = map snd ablations ++ ["allAblationsRemainFlatDyadic", "allAblationsCarryGlobalOptimizerL2"]
  source <- readFile path
  let missing = filter (\symbol -> not (symbol `isInfixOf` source)) required
  if not (null missing)
    then pure (MissingProof, missing)
    else do
      (code, _out, err) <- readProcessWithExitCode "agda" ["--safe", path] ""
      case code of
        ExitSuccess -> pure (Proven, [])
        ExitFailure _ -> pure (AgdaFailure, [err])

renderCandidateModule :: [(String, String, String, Status, [String])] -> Status -> String -> String
renderCandidateModule results ablationStatus ablationDetails =
  unlines $
    [ "{-# OPTIONS --safe #-}"
    , "module Exotic.ERL.Exploration.Generated.ExplorationCandidates where"
    , ""
    , "open import Agda.Builtin.Nat using (Nat)"
    , ""
    , "-- Generated flat-dyadic theorem-discovery report."
    , "-- Agda remains the only acceptance oracle."
    , "-- External CHAD references below are discovery/specification metadata only."
    , ""
    ]
    ++ concatMap renderCHADReference chadReferences
    ++ [ "" ]
    ++ concatMap render results
    ++ [ "-- ablation surface status: " ++ show ablationStatus
       , "-- ablation surface details: " ++ intercalate " | " ablationDetails
       ]
    ++ concatMap renderAblation ablations
    ++ [ "flatDyadicLawMethodPermutationCount : Nat"
       , "flatDyadicLawMethodPermutationCount = 3"
       , "flatDyadicAblationVariantCount : Nat"
       , "flatDyadicAblationVariantCount = 5"
       ]
  where
    renderCHADReference (variant, reference, role) =
      [ "-- CHAD variant: " ++ variant
      , "-- reference: " ++ reference
      , "-- role: " ++ role
      , ""
      ]

    render (lawName, lawTag, methodName, status, details) =
      [ "-- law: " ++ lawName ++ " (" ++ lawTag ++ ")"
      , "-- method: " ++ methodName
      , "-- status: " ++ show status
      , "-- details: " ++ intercalate " | " details
      , ""
      ]

    renderAblation (name, constructorName) =
      [ "-- flat-dyadic ablation: " ++ name
      , "-- constructor: " ++ constructorName
      , "-- global optimizer/L2: always-on"
      , "-- norm-pair scope: learned nonlinearities only"
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
  (ablationStatus, ablationDetails) <- checkAblationFile
  writeFile "Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda"
    (renderCandidateModule results ablationStatus ablationDetails)
  mapM_ printResult results
  putStrLn $
    "ablations=status=" ++ show ablationStatus
    ++ if null ablationDetails then "" else ",details=" ++ intercalate ";" ablationDetails
  if any (\(_, _, _, status, _) -> status /= Proven) results
      || ablationStatus /= Proven
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
