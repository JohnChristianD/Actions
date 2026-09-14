{-# OPTIONS --safe #-}

module Exotic.econlib.Optimization where

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8; int8OfNat; code)

------------------------------------------------------------------------
-- Finite dyadic/int8 optimization fragment.
-- Finite feasible set, exact objective values, and certified argmax.
------------------------------------------------------------------------

record FiniteProblem2 : Set where
  constructor finiteProblem2
  field
    value₀ value₁ : Int8

open FiniteProblem2 public

objective : FiniteProblem2 → Fin 2 → Int8
objective p zero = value₀ p
objective p (suc zero) = value₁ p

score : FiniteProblem2 → Fin 2 → ℕ
score p i = toℕ (code (objective p i))

record IsArgmax (p : FiniteProblem2) (i : Fin 2) : Set where
  constructor isArgmax
  field
    dominates : ∀ j → score p j ≤ score p i

canonicalProblem : FiniteProblem2
canonicalProblem = finiteProblem2 (int8OfNat 3) (int8OfNat 7)

canonicalArgmax : IsArgmax canonicalProblem (suc zero)
canonicalArgmax = isArgmax λ where
  zero → s≤s (s≤s (s≤s (s≤s z≤n)))
  suc zero → refl

finiteOptimizer : FiniteProblem2 → Fin 2
finiteOptimizer p = if score p zero ≤ score p (suc zero)
  then suc zero
  else zero

canonicalOptimizer : finiteOptimizer canonicalProblem ≡ suc zero
canonicalOptimizer = refl
