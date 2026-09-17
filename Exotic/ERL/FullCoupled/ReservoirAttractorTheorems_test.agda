{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ReservoirAttractorTheorems_test where

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L
open import Exotic.ERL.FullCoupled.GeneralReservoirAttractorTheorems as R

finite-core-cycle : ∀ (S : L.Int8 → L.Int8) (s : L.Int8) →
  R.FiniteOrbitCollision S s
finite-core-cycle = R.finiteCore-collision

finite-core-tail : ∀ (S : L.Int8 → L.Int8) (s : L.Int8) →
  R.FiniteOrbitTailRepeat S s
finite-core-tail = R.finiteCore-tail-repeat

l1-progress-regression : ∀ (n : L.NormPair) w x →
  L.l1Weight n ≤ L.l1Weight (L.normStep n w x)
l1-progress-regression = R.l1Weight-step-monotone

contextual-recall-regression : ∀ {S M C : Set}
  (W : R.MultiAttractorReservoir S M C) (m : M) →
  R.BasinHit S (R.step′ W) (R.attractor′ W m) (R.cue′ W m)
contextual-recall-regression = R.contextualRecall
