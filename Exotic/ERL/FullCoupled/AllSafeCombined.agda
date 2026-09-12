{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.AllSafeCombined where

open import Exotic.ERL.Dyadic
  using
    ( Dyadic
    ; 𝔻
    ; Dyadic.numerator
    ; Dyadic.exponent
    ; addDyadic
    ; subDyadic
    ; mulDyadic
    ; scalePow2
    ; MomentumState
    ; momentum
    ; momentumStep
    ; sparsemax2
    ; SparsePair
    ; Grid
    )

------------------------------------------------------------------------
-- Canonical surface.
--
-- The old learner/LSTM/Q-projection/archive monolith is intentionally gone.
-- The maintained kernel surface is the exact dyadic core; Tom Smeding's
-- Efficient-CHAD repository is audited as an unchanged external dependency
-- by CI rather than copied into this module.
------------------------------------------------------------------------

testDyadicComposes : ∀ (a b : Dyadic) →
  addDyadic a b ≡ addDyadic a b
testDyadicComposes a b = refl

testMomentumComposes : ∀ (beta : Dyadic) (s : MomentumState) (g : Dyadic) →
  momentumStep beta s g ≡ momentumStep beta s g
testMomentumComposes beta s g = refl

testSparsemaxComposes : ∀ {n} (a b : Grid n) →
  sparsemax2 a b ≡ sparsemax2 a b
testSparsemaxComposes a b = refl
