{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v159_test where

open import Agda.Builtin.Equality using (_≡_)
open import Exotic.ERL.FullCoupled.EfficientCHAD_v159

base2RoundTripTest : ∀ {A : FiniteOrderedAlgebra} (xs : FeatureVec A) →
  idbdLog2 A (idbdPow2 A xs) ≡ xs
base2RoundTripTest = idbdBase2RoundTrip

couplingWitnessTest : ∀ {A : FiniteOrderedAlgebra}
  (s : FullFiniteOrderedRationalLearner A) →
  FullFiniteOrderedRationalCoupling A
couplingWitnessTest = fullLearnerCouplingWitness

emergentGeometryTest : ∀ {A : FiniteOrderedAlgebra} (x : R A) →
  EmergentGeometry A x
emergentGeometryTest = emergentGeometry _
