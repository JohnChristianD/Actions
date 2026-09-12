{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage01_FiniteAlgebra where

-- Kernel checkpoint marker: this stage remains primitive finite algebra.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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
