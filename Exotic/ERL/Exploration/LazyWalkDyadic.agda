{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.LazyWalkDyadic where

open import Data.Nat using (ℕ)
open import Agda.Builtin.Equality using (_≡_; refl)

data LazyOutcome : Set where
  lazyStay : LazyOutcome
  lazyForward : LazyOutcome
  lazyBackward : LazyOutcome

lazyWeight : LazyOutcome → ℕ
lazyWeight lazyStay = 2
lazyWeight lazyForward = 1
lazyWeight lazyBackward = 1

lazyDenominator : ℕ
lazyDenominator = 4

lazyWeight-sum :
  lazyWeight lazyStay + lazyWeight lazyForward + lazyWeight lazyBackward
  ≡ lazyDenominator
lazyWeight-sum = refl

lazyStay-positive : lazyWeight lazyStay ≡ 2
lazyStay-positive = refl

lazyForward-positive : lazyWeight lazyForward ≡ 1
lazyForward-positive = refl

lazyBackward-positive : lazyWeight lazyBackward ≡ 1
lazyBackward-positive = refl

-- The common denominator is a power of two, so every mass is exactly dyadic.
lazyProbability-numerator : LazyOutcome → ℕ
lazyProbability-numerator = lazyWeight

lazyProbability-normalized :
  lazyProbability-numerator lazyStay
  + lazyProbability-numerator lazyForward
  + lazyProbability-numerator lazyBackward
  ≡ 4
lazyProbability-normalized = refl
