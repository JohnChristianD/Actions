{-# OPTIONS --safe #-}
module Exotic.efficient_chad.FiniteDivision where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin using (toℕ)
open import Data.Nat.DivMod using (_/_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8OfNat
  )

------------------------------------------------------------------------
-- Minimal finite division layer.
-- Pattern-matching PositiveNat exposes the suc-shaped divisor to Agda's
-- standard NonZero instance. This is quotient arithmetic only, not a field.
------------------------------------------------------------------------

data PositiveNat : Set where
  positive : Nat → PositiveNat

positiveValue : PositiveNat → Nat
positiveValue (positive n) = suc n

finiteDivideNat : Nat → PositiveNat → Nat
finiteDivideNat numerator (positive n) = numerator / suc n

finiteDivideInt8 : Int8 → PositiveNat → Int8
finiteDivideInt8 x denominator =
  int8OfNat (finiteDivideNat (toℕ (code x)) denominator)

finiteDivide-two-step :
  ∀ (x : Int8) (d : PositiveNat) →
  finiteDivideInt8 x d ≡
  int8OfNat ((toℕ (code x)) / positiveValue d)
finiteDivide-two-step x (positive n) = refl
