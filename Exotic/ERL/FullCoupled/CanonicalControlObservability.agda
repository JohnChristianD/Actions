{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalControlObservability where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith

record ReachabilityWitness {S : Set}
  (step : S → S) (s t : S) : Set where
  constructor reachableAt
  field
    steps : Nat
    endpoint : iterate step steps s ≡ t

CanonicalReachable : FullLearnerKernel → FullLearnerState → FullLearnerState → Set
CanonicalReachable K s t =
  ReachabilityWitness (canonicalFullStep K) s t

canonicalOrbitReachable : ∀ K s n →
  CanonicalReachable K s (iterateCanonical K n s)
canonicalOrbitReachable K s n = reachableAt n refl

canonicalSuccessorReachable : ∀ K s →
  CanonicalReachable K s (canonicalFullStep K s)
canonicalSuccessorReachable K s = reachableAt (suc zero) refl

CanonicalOrbitControllable : FullLearnerKernel → FullLearnerState → Set
CanonicalOrbitControllable K s =
  ∀ n → CanonicalReachable K s (iterateCanonical K n s)

canonicalOrbitControllable : ∀ K s → CanonicalOrbitControllable K s
canonicalOrbitControllable K s = canonicalOrbitReachable K s

fullStateObservation : FullLearnerState → FullLearnerState
fullStateObservation s = s

fullStateObservation-injective : ∀ s t →
  fullStateObservation s ≡ fullStateObservation t → s ≡ t
fullStateObservation-injective s t h = h

clockObservation : FullLearnerState → Nat
clockObservation s = clock s

clockObservation-after-iterate : ∀ K s n →
  clockObservation (iterateCanonical K n s) ≡ clock s + n
clockObservation-after-iterate = clockAfter

clockObservation-separates-clock : ∀ s t →
  clockObservation s ≡ clockObservation t → clock s ≡ clock t
clockObservation-separates-clock s t h = h
