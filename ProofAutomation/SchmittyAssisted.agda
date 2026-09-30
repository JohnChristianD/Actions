{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}

module ProofAutomation.SchmittyAssisted where

open import Data.Integer using (ℤ; _+_; _-_; _*_)
open import Data.Unit using ()
open import Relation.Binary.PropositionalEquality using (_≡_)
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

schmitty-integer-polynomial-normalization :
  (i : ℤ) → (i + 2) * (i + -2) ≡ i * i - 4
schmitty-integer-polynomial-normalization = solveZ3
