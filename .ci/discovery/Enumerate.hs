module Main where

import System.Directory (createDirectoryIfMissing)
import Control.Monad (forM_)

data Candidate = Candidate
  { moduleName :: String
  , fileStem :: String
  , imports :: String
  , proposition :: String
  , proofTerm :: String
  }

unitNoise :: Candidate
unitNoise = Candidate
  "DtriUnitSupport"
  "dtri-unit-support"
  "open import Exotic.ERL.Exploration.FiniteNoise using (unitMinusWitness; unitPlusWitness)"
  "(noiseCode neg ≡ int8OfNat 255) × (noiseCode pos ≡ one8)"
  "unitMinusWitness , unitPlusWitness"

-- Candidates are generated from a finite algebraic grammar, then accepted
-- only if the Agda kernel checks the resulting proposition.
candidates :: [Candidate]
candidates =
  [ unitNoise
  , Candidate
      "DtriNormalises"
      "dtri-normalises"
      "open import Exotic.ERL.Exploration.FiniteNoise using (totalWeight)"
      "totalWeight ≡ 256"
      "totalWeight"
  , Candidate
      "DtriZeroMass"
      "dtri-zero-mass"
      "open import Exotic.ERL.Exploration.FiniteNoise using (weight; zero; zeroHasPositiveMass)"
      "weight zero ≡ 16"
      "zeroHasPositiveMass"
  , Candidate
      "PopulationAxes"
      "population-axes"
      "open import Exotic.ERL.Exploration.CanonicalMR15GA using (populationSize; dimension)"
      "populationSize * dimension ≡ 64"
      "refl"
  , Candidate
      "OneFifthThreshold3"
      "one-fifth-threshold-3"
      "open import Exotic.ERL.Exploration.CanonicalMR15GA using (oneFifthStepUpdate; initialExponent; lowerExponent)\nopen import Data.Fin using (Fin)"
      "oneFifthStepUpdate initialExponent (Fin.suc (Fin.suc (Fin.suc Fin.zero))) ≡ lowerExponent initialExponent"
      "refl"
  , Candidate
      "OneFifthThreshold4"
      "one-fifth-threshold-4"
      "open import Exotic.ERL.Exploration.CanonicalMR15GA using (oneFifthStepUpdate; initialExponent; raiseExponent)\nopen import Data.Fin using (Fin)"
      "oneFifthStepUpdate initialExponent (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) ≡ raiseExponent initialExponent"
      "refl"
  , Candidate
      "LearnerSelfLoop"
      "learner-self-loop"
      "open import Exotic.ERL.FullCoupled.CanonicalLearner using (start; step; zeroSelfLoop)\nopen import Exotic.ERL.Exploration.FiniteNoise using (zero)\nopen import Exotic.ERL.FullCoupled.CanonicalToken using (token)\nopen import Exotic.efficient_chad.Int8 using (zero8)"
      "step start zero zero (token zero8 zero8 zero8 zero8) (token zero8 zero8 zero8 zero8) zero8 ≡ start"
      "zeroSelfLoop"
  , Candidate
      "CoupledSelfLoop"
      "coupled-self-loop"
      "open import Exotic.ERL.FullCoupled.CanonicalLearnerEA using (startCoupled; coupledStep; noPerturb; zeroNoiseTape; zeroCoordinateTape)\nopen import Exotic.ERL.Exploration.FiniteNoise using (zero)\nopen import Exotic.efficient_chad.Int8 using (zero8)"
      "coupledStep startCoupled noPerturb zero zero zeroNoiseTape zeroCoordinateTape zero8 ≡ startCoupled"
      "refl"
  , Candidate
      "BadHaarSquare"
      "bad-haar-square"
      "open import Exotic.ERL.Representation.Haar2 using (HaarPair; haarPair; haar2)"
      "∀ x y → haar2 (haar2 (haarPair x y)) ≡ haarPair x y"
      "refl"
  ]

sourceFor :: Candidate -> String
sourceFor c =
  "{-# OPTIONS --safe #-}\n"
  ++ "module " ++ moduleName c ++ " where\n\n"
  ++ "open import Agda.Builtin.Equality using (_≡_; refl)\n"
  ++ "open import Data.Product using (_×_; _,_)\n"
  ++ "open import Exotic.efficient_chad.Int8 using (Int8; int8OfNat; one8)\n"
  ++ "open import Exotic.ERL.Exploration.FiniteNoise using (Noise; noiseCode; neg; pos; zero)\n"
  ++ imports c ++ "\n\n"
  ++ "candidate : " ++ proposition c ++ "\n"
  ++ "candidate = " ++ proofTerm c ++ "\n"

main :: IO ()
main = do
  let root = ".ci/generated-conjectures"
  createDirectoryIfMissing True root
  forM_ candidates $ \c ->
    writeFile (root ++ "/" ++ fileStem c ++ ".agda") (sourceFor c)
