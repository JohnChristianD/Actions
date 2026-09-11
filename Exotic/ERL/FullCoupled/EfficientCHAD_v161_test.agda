{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v161_test where

open import Agda.Builtin.Equality using (_≡_)
open import Exotic.ERL.FullCoupled.EfficientCHAD_v161

base2Test : ∀ {A : FiniteOrderedRational} (xs : FeatureVec A) →
  idbdLog2 A (idbdPow2 A xs) ≡ xs
base2Test = idbdBase2RoundTrip

couplingTest : ∀ {A : FiniteOrderedRational} →
  FullFiniteOrderedRationalCoupling A
couplingTest = fullFiniteOrderedRationalCoupling

actorTest : ∀ {A : FiniteOrderedRational} x →
  evalActorAction {A = A} identityActor x ≡ x
actorTest = canonicalActorIdentity
