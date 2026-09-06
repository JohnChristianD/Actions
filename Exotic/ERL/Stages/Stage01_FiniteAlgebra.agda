{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage01_FiniteAlgebra where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _≟_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)

record FiniteAlgebra : Set₁ where
  field
    carrier : Set
    zeroA oneA : carrier
    addA mulA : carrier → carrier → carrier

natAlgebra : FiniteAlgebra
natAlgebra = record
  { carrier = Nat
  ; zeroA = zero
  ; oneA = suc zero
  ; addA = _+_
  ; mulA = _*_
  }

zeroAdd : ∀ n → zero + n ≡ n
zeroAdd n = refl

zeroMul : ∀ n → zero * n ≡ zero
zeroMul n = refl

finiteDecision : ∀ a b → Bool
finiteDecision a b with a ≟ b
... | true = true
... | false = false
