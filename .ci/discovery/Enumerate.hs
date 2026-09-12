module Main where

import System.Directory (createDirectoryIfMissing)

candidates :: [(String, String, String, String, String)]
candidates =
  [ ("HaarSquare", "haar-square", "open import Exotic.ERL.Representation.Haar2 using (HaarPair; haarPair; haar2-square-scale)",
     "∀ x y → haar2 (haar2 (haarPair x y)) ≡ haarPair (x + x) (y + y)",
     "haar2-square-scale")
  , ("NoiseNormalises", "noise-normalises", "open import Exotic.ERL.Exploration.FiniteNoise using (weight; neg; zero; pos)",
     "weight neg + weight zero + weight pos ≡ 4",
     "refl")
  , ("NoiseSelfLoop", "noise-self-loop", "open import Exotic.ERL.Exploration.FiniteMarkov using (transition; selfLoopExample)\nopen import Exotic.ERL.Exploration.FiniteNoise using (zero)\nopen import Exotic.efficient_chad.Int8 using (one8)",
     "transition zero one8 ≡ one8",
     "selfLoopExample")
  , ("ComposedZero", "composed-zero", "open import Exotic.ERL.Exploration.ComposedLearnerExploration using (zeroStep-is-initial; zeroStep)\nopen import Exotic.ERL.Finite.TrueOnlineTD using (initialState)",
     "zeroStep ≡ initialState",
     "zeroStep-is-initial")
  , ("FullLearnerTotal", "full-learner-total", "open import Exotic.ERL.FullCoupled.FiniteLearner using (Parameters; Window2; learnForward)\nopen import Exotic.efficient_chad.Int8 using (Int8)",
     "(p : Parameters) → (w : Window2) → Int8",
     "learnForward")
  , ("BadHaarSquare", "bad-haar-square", "open import Exotic.ERL.Representation.Haar2 using (HaarPair; haarPair; haar2)",
     "∀ x y → haar2 (haar2 (haarPair x y)) ≡ haarPair x y",
     "refl")
  ]

sourceFor :: String -> String -> String -> String -> String -> String
sourceFor moduleName imports proposition proof =
  "{-# OPTIONS --safe #-}\n"
  ++ "module " ++ moduleName ++ " where\n\n"
  ++ "open import Agda.Builtin.Equality using (_≡_; refl)\n"
  ++ "open import Data.Integer.Base using (Int; _+_)\n"
  ++ imports ++ "\n\n"
  ++ "candidate : " ++ proposition ++ "\n"
  ++ "candidate = " ++ proof ++ "\n"

main :: IO ()
main = do
  let root = ".ci/generated-conjectures"
  createDirectoryIfMissing True root
  mapM_ emit candidates
  where
  emit (moduleName, fileStem, imports, proposition, proof) =
    writeFile
      (root ++ "/" ++ fileStem ++ ".agda")
      (sourceFor moduleName imports proposition proof)
  root = ".ci/generated-conjectures"
