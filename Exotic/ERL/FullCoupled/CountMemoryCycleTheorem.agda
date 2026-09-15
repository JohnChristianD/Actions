{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CountMemoryCycleTheorem where

open import Agda.Builtin.Equality using (_≡_; sym; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_<_; _≤_; z≤n; s≤s)

lt-trans : ∀ {a b c : Nat} → a < b → b < c → a < c
lt-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)
  where
  le-trans : ∀ {m n k : Nat} → m ≤ n → n ≤ k → m ≤ k
  le-trans z≤n q = q
  le-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)

lt-irrefl : ∀ n → ¬ (n < n)
lt-irrefl zero ()
lt-irrefl (suc n) (s≤s p) = lt-irrefl n p

record StrictCountSystem (S : Set) (step : S → S) : Set₁ where
  constructor strictCountSystem
  field
    count : S → Nat
    strictCount : ∀ s → step s ≢ s → count s < count (step s)
open StrictCountSystem public

count-two-step-increases :
  ∀ {S : Set} {step : S → S} (C : StrictCountSystem S step)
  {s : S} →
  step s ≢ s →
  step (step s) ≢ step s →
  count C s < count C (step (step s))
count-two-step-increases C nf0 nf1 =
  lt-trans (strictCount C _ nf0) (strictCount C _ nf1)

noCountedTwoCycle :
  ∀ {S : Set} {step : S → S} (C : StrictCountSystem S step)
  {s : S} →
  step (step s) ≡ s →
  step s ≢ s →
  step (step s) ≢ step s →
  ⊥
noCountedTwoCycle C cyc nf0 nf1 =
  lt-irrefl (count C s)
    (trans
      (count-two-step-increases C nf0 nf1)
      (sym (cong-count cyc)))
  where
  cong-count : ∀ {x y : S} → x ≡ y → count C x ≡ count C y
  cong-count refl = refl

-- Strictly increasing unbounded count memory is therefore enough to exclude
-- every 2-cycle, including on an infinite state carrier.  It does not imply
-- finite-time convergence: the count may continue increasing forever.
