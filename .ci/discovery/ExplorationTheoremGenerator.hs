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
  , Surface "Exotic/ERL/FullCoupled/FiniteNormAlgebra.agda"
      [ "l1WeightNorm", "onePathNorm", "finiteNormOrder", "finiteNormAlgebra-is-ordered" ]
  , Surface "Exotic/ERL/FullCoupled/CanonicalControlObservability.agda"
      [ "canonicalOrbitReachable", "canonicalOrbitControllable"
      , "fullStateObservation-injective", "clockObservation-after-iterate" ]
  , Surface "Exotic/ERL/FullCoupled/CNNLogPyramidPreservation.agda"
      [ "CNNLogPyramid64", "cnnToAttention", "cnnLogPyramidEquivalent-trans"
      , "cnnLogPyramidGRUInputPreservation", "cnnLogPyramidCommutesWithCanonicalGRU"
      , "cnnLogPyramidEncoding-preserves-input" ]
  , Surface "Exotic/ERL/FullCoupled/CanonicalLearnerGameExecution_test.agda"
      [ "learnerRewardStep-reward-insensitive", "closedLoopInput-roundtrip"
      , "closedLoopReward-roundtrip", "closedLoopLeftRewardLearns"
      , "closedLoopRightRewardLearns", "closedLoopStep-clock"
      , "check-knapsack-return", "check-knapsack-regret", "check-knapsack-success"
      , "check-maze-return", "check-maze-regret", "check-maze-success"
      , "check-meta-maze-return", "check-meta-maze-regret", "check-meta-maze-success"
      , "check-four-rooms-return", "check-four-rooms-regret", "check-four-rooms-success"
      , "check-cartpole-return", "check-cartpole-regret"
      , "check-bandit-best0-return", "check-bandit-best0-regret", "check-bandit-best0-success"
      , "check-bandit-best1-return", "check-bandit-best1-regret", "check-bandit-best1-success" ]
  , Surface "Exotic/econlib/GameTheory.agda"
      [ "isNashEquilibriumDD", "pdIter-stabilises", "nashConvergenceWitness" ]
  , Surface "Exotic/econlib/Equilibrium.agda"
      [ "canonicalEconomy2Equilibrium", "clearIter-stabilises", "canonicalProductionEquilibrium2" ]
  , Surface "Exotic/econlib/MatchingPennies.agda"
      [ "matchingPennies", "matchingPennies-no-pure", "matchingPennies-no-stable-pure-profile" ]
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
      putStrLn "finite-norm-algebra=complete"
      putStrLn "control-observability-surface=complete"
      putStrLn "cnn-log-pyramid-preservation=complete"
      putStrLn "closed-loop-game-bench=complete"
      putStrLn "econlib-game-theory=complete"
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
