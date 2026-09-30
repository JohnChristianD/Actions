{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}

module ProofAutomation.SchmittyAssisted where

open import Data.Integer using (ℤ; _+_; _-_; _*_; _>_; _<_; _≥_; _≤_; +<+)
open import Data.Nat using (s≤s; z≤n)
open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import SMT.Theories.Ints as Ints
open import SMT.Backend.Z3 Ints.reflectable

import Data.Integer.Literals as Int using (number; negative)

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg

instance _ = Int.number
         _ = Int.negative

schmitty-integer-associativity :
  (i j k : ℤ) → i + (j + k) ≡ (i + j) + k
schmitty-integer-associativity = solveZ3

schmitty-integer-layernorm-expansion :
  (i scale : ℤ) → (i + 2) * scale ≡ i * scale + scale + scale
schmitty-integer-layernorm-expansion = solveZ3

check-schmitty-compute :
  (H : 2 ≤ 2) →
  ((2 : ℤ) * 2 > 0)
check-schmitty-compute _ = +<+ (s≤s z≤n)
