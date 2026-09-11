{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v158_test where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)

open import Exotic.ERL.FullCoupled.EfficientCHAD_v158

base2RoundTripTest : ∀ {A : OrderedAlgebra} (xs : FeatureVec A) →
  idbdLog2 A (idbdPow2 A xs) ≡ xs
base2RoundTripTest = idbdBase2RoundTrip

fullCouplingClosureTest : ∀ {A : OrderedAlgebra} →
  FullFiniteOrderedRationalCoupling A
fullCouplingClosureTest = fullFiniteOrderedRationalCoupling

emergentCompositionTest : ∀ {A : OrderedAlgebra} (x : R A) →
  emergentGeometryLaw A x
emergentCompositionTest = emergentGeometryLaw
