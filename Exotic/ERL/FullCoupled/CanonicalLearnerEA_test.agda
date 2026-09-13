{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearnerEA_test where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Fin as F using (Fin)
open import Exotic.ERL.Exploration.CanonicalMR15GA using
  ( initialMR15
  ; neutralGeneration
  )
open import Exotic.ERL.Exploration.FiniteNoise using (zero)
open import Exotic.ERL.FullCoupled.CanonicalLearnerEA

coupledStartSelfLoopTest :
  coupledStep
    startCoupled
    noPerturb
    zero
    zero
    zeroNoiseTape
    zeroCoordinateTape
    rewardZero
  ≡ startCoupled
coupledStartSelfLoopTest = refl

coupledSelfLoopWitnessTest :
  CoupledEdge startCoupled startCoupled
coupledSelfLoopWitnessTest = startCoupledSelfLoop

neutralGenerationTest :
  neutralGeneration
    (λ _ → 0)
  ≡ neutralGeneration (λ _ → 0)
neutralGenerationTest = refl

coupledReachReflexive : ∀ (s : CoupledState) →
  CoupledReach s s
coupledReachReflexive s = here
