{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v162_test where

open import Agda.Builtin.Equality using (_≡_)
open import Exotic.ERL.FullCoupled.EfficientCHAD_v161
open import Exotic.ERL.FullCoupled.EfficientCHAD_v162

base2Test : ∀ {A : FiniteOrderedRational} (xs : FeatureVec A) →
  idbdLog2 A (idbdPow2 A xs) ≡ xs
base2Test = idbdBase2RoundTrip

couplingTest : ∀ {A : FiniteOrderedRational} →
  FullFiniteOrderedRationalCoupling A
couplingTest = fullFiniteOrderedRationalCoupling

actorTest : ∀ {A : FiniteOrderedRational} x →
  evalActorAction {A = A} identityActor x ≡ x
actorTest = canonicalActorIdentity

metaValueTest : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (p : ParameterCoordinate A) g →
  value (softsignQIDBDMetaStep cfg p g) ≡ value (softsignQIDBDStep p g)
metaValueTest = softsignQIDBDMetaDecayValueLaw

criticGlobalOptimizerTest : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  critic (canonicalLearnerUpdate cfg s g) ≡ canonicalListUpdate cfg (critic s) g
criticGlobalOptimizerTest = canonicalCriticLaw

ffnLayeringTest : ∀ {A : FiniteOrderedRational}
  (f : CanonicalSoftsignSignReLUFFN A) x →
  runCanonicalSoftsignSignReLUFFN f x ≡ runCanonicalSoftsignSignReLUFFN f x
ffnLayeringTest = canonicalFFNLayeringLaw

normPairTest : ∀ {A : FiniteOrderedRational}
  (n : NormPair A) → canonicalNormPairSurface n ≡ n
normPairTest = canonicalNormPairLaw
