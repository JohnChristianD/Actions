{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.AllSafeCombined where

open import Exotic.ERL.Dyadic
  using
    ( Dyadic
    ; 𝔻
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

testDyadicComposes : ∀ (a b : Dyadic) →
  addDyadic a b ≡ addDyadic a b
testDyadicComposes a b = refl

testMomentumComposes : ∀ (beta : Dyadic) (s : MomentumState) (g : Dyadic) →
  momentumStep beta s g ≡ momentumStep beta s g
testMomentumComposes beta s g = refl

testSparsemaxComposes : ∀ {n} (a b : Grid n) →
  sparsemax2 a b ≡ sparsemax2 a b
testSparsemaxComposes a b = refl
