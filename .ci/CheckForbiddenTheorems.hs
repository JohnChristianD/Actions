module Main where

import Control.Monad (forM_)
import Data.List (isInfixOf)
import System.Directory (doesFileExist)
import System.Exit (exitFailure, exitSuccess)

checkedPaths :: [FilePath]
checkedPaths =
  [ "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda"
  , "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda"
  , "Exotic/ERL/FullCoupled/CanonicalGamePorts.agda"
  , "Exotic/ERL/FullCoupled/CanonicalFaithfulGameVariants.agda"
  , "Exotic/ERL/FullCoupled/FiniteParameterCompleteness.agda"
  , "Exotic/ERL/FullCoupled/FiniteNormAlgebra.agda"
  , "Exotic/ERL/FullCoupled/CanonicalControlObservability.agda"
  , "Exotic/ERL/FullCoupled/CanonicalLearnerGameExecution_test.agda"
  , "Exotic/ERL/FullCoupled/CNNLogPyramidPreservation.agda"
  , "Exotic/econlib/GameTheory.agda"
  , "Exotic/econlib/Equilibrium.agda"
  , "Exotic/econlib/MatchingPennies.agda"
  , "Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda"
  ]

forbidden :: [String]
forbidden =
  [ "transcendental"
  , "transcendentals"
  , "flatdyadicmix"
  , "postulate"
  , "{-# postulate"
  , "{!"
  , "!!}"
  , "?hole?"
  ]

main :: IO ()
main = do
  missing <- fmap concat (mapM missingFile checkedPaths)
  problems <- fmap concat (mapM inspect checkedPaths)
  let allProblems = missing ++ problems
  if null allProblems
    then do
      putStrLn "canonical-safe-surface=complete"
      putStrLn "holes-and-postulates=absent"
      putStrLn "forbidden-theorem-families=absent"
      exitSuccess
    else do
      forM_ allProblems (putStrLn . ("ERROR: " ++))
      exitFailure
  where
    missingFile path = do
      ok <- doesFileExist path
      pure ["required canonical proof file missing: " ++ path | not ok]

    inspect path = do
      source <- readFile path
      let lower = map toLowerAscii source
          forbiddenLower = map (map toLowerAscii) forbidden
      pure
        [ "forbidden token in " ++ path ++ ": " ++ token
        | token <- forbiddenLower
        , token `isInfixOf` lower
        ]

    toLowerAscii c
      | c >= 'A' && c <= 'Z' = toEnum (fromEnum c + 32)
      | otherwise = c
