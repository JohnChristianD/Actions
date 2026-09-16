module Main where

import Data.List (isInfixOf)
import System.Exit (ExitCode(..), exitFailure, exitSuccess)
import System.Process (readProcessWithExitCode)

data Surface = Surface FilePath [String]

surfaces :: [Surface]
surfaces =
  [ Surface "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda"
      [ "int8StateSpace", "walshHadamardOrthogonality4", "canonicalWalshWidth-power4"
      , "fullLearnerInt8CoordinateCount-law", "canonicalFullStep-clock" ]
  , Surface "Exotic/ERL/FullCoupled/CanonicalGamePorts.agda"
      [ "jumanjiKnapsackPort", "jumanjiMazeV0Port", "jumanjiLevelBasedForagingV0Port"
      , "gymnaxMetaMazePort", "gymnaxFourRoomsPort", "gymnaxPongMiscPort"
      , "gymnaxMemoryChainBsuitePort", "gymnaxDiscountingChainBsuitePort"
      , "gymnaxCartPolePort", "gymnaxBernoulliBanditMiscPort", "pobaxRockSamplePort" ]
  , Surface "Exotic/ERL/FullCoupled/CanonicalFaithfulGameVariants.agda"
      [ "fourRoomsOpenExact", "toyMazeOpenExact" ]
  , Surface "Exotic/ERL/FullCoupled/FiniteParameterCompleteness.agda"
      [ "learnerDefaultD", "learnerDefaultD-power4", "parameterize-complete"
      , "parameterizeFin-complete", "finiteStateFunctionalCompleteness" ]
  , Surface "Exotic/ERL/FullCoupled/CanonicalControlObservability.agda"
      [ "canonicalOrbitReachable", "canonicalOrbitControllable"
      , "fullStateObservation-injective", "clockObservation-after-iterate" ]
  , Surface "Exotic/ERL/FullCoupled/CNNLogPyramidPreservation.agda"
      [ "CNNLogPyramid64", "cnnToAttention", "cnnLogPyramidGRUInputPreservation"
      , "cnnLogPyramidCommutesWithCanonicalGRU" ]
  , Surface "Exotic/ERL/FullCoupled/CanonicalLearnerGameExecution_test.agda"
      [ "learnerRewardStep-clock", "check-knapsack", "check-maze", "check-lbf"
      , "check-meta-maze", "check-four-rooms", "check-pong", "check-memory-chain"
      , "check-discounting-chain", "check-cartpole", "check-bandit", "check-rocksample" ]
  , Surface "Exotic/econlib/GameTheory.agda"
      [ "isNashEquilibriumDD", "pdIter-stabilises", "nashConvergenceWitness" ]
  ]

missingSymbols :: Surface -> IO [String]
missingSymbols (Surface path symbols) = do
  source <- readFile path
  pure [ path ++ ": " ++ s | s <- symbols, not (s `isInfixOf` source) ]

runAgda :: FilePath -> IO (Maybe String)
runAgda path = do
  (code, out, err) <- readProcessWithExitCode "agda" ["--safe", path] ""
  case code of
    ExitSuccess -> pure Nothing
    ExitFailure _ -> pure (Just (path ++ ": " ++ err ++ out))

main :: IO ()
main = do
  missing <- fmap concat (mapM missingSymbols surfaces)
  failures <- fmap concat $ mapM (fmap maybeToList . runAgda . surfacePath) surfaces
  let problems = missing ++ failures
  if null problems
    then do
      putStrLn "canonical-surfaces=complete"
      putStrLn "finite-function-parameter-theorem=complete"
      putStrLn "control-observability-surface=complete"
      putStrLn "cnn-log-pyramid-preservation=complete"
      putStrLn "game-execution-regression=complete"
      writeFile "Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda"
        "{-# OPTIONS --safe #-}\nmodule Exotic.ERL.Exploration.Generated.ExplorationCandidates where\n-- Generated canonical closure status: Proven\n"
      exitSuccess
    else do
      mapM_ (putStrLn . ("ERROR: " ++)) problems
      exitFailure
  where
    surfacePath (Surface p _) = p
    maybeToList Nothing = []
    maybeToList (Just x) = [x]
