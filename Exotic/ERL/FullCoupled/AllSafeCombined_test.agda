{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.AllSafeCombined_test where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Dyadic

canonicalDyadicEquality : ∀ (x y : Dyadic) → addDyadic x y ≡ addDyadic x y
canonicalDyadicEquality x y = refl

canonicalMomentumEquality : ∀ (beta : Dyadic) (s : MomentumState) (g : Dyadic) →
  momentumStep beta s g ≡ momentumStep beta s g
canonicalMomentumEquality beta s g = refl

canonicalSparsemaxEquality : ∀ {n} (a b : Grid n) →
  sparsemax2 a b ≡ sparsemax2 a b
canonicalSparsemaxEquality a b = refl
