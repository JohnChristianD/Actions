{-# OPTIONS --safe #-}

module Exotic.econlib.Optimization where

open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8; int8OfNat; code)
open import Data.Fin using (toℕ)

------------------------------------------------------------------------
-- Finite dyadic/int8 optimization fragment.
-- This is the discrete analogue of Econlib's optimization surface:
-- finite feasible set, exact objective values, and certified argmax.
------------------------------------------------------------------------

record FiniteProblem2 : Set where
  constructor finiteProblem2
  field
    value₀ value₁ : Int8

open FiniteProblem2 public

objective : FiniteProblem2 → ℕ → Int8
objective p zero = value₀ p
objective p (suc _) = value₁ p

score : FiniteProblem2 → ℕ → ℕ
score p i = toℕ (code (objective p i))

record IsArgmax (p : FiniteProblem2) (i : ℕ) : Set where
  constructor isArgmax
  field
    dominates : ∀ j → score p j ≤ score p i

canonicalProblem : FiniteProblem2
canonicalProblem = finiteProblem2 (int8OfNat 3) (int8OfNat 7)

canonicalArgmax : IsArgmax canonicalProblem 1
canonicalArgmax = isArgmax λ where
  zero → s≤s (s≤s (s≤s (s≤s z≤n)))
  suc zero → refl
  suc (suc _) → refl

finiteOptimizer : FiniteProblem2 → ℕ
finiteOptimizer p = if score p 0 ≤ score p 1 then 1 else 0

canonicalOptimizer : finiteOptimizer canonicalProblem ≡ 1
canonicalOptimizer = refl
