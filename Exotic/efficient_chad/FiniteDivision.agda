{-# OPTIONS --safe #-}
module Exotic.efficient_chad.FiniteDivision where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (toℕ)
open import Data.Nat using (Nat; suc)
open import Data.Nat.DivMod using (_/_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8OfNat
  )

------------------------------------------------------------------------
-- Minimal finite division layer.
-- This is not a field or local-ring construction. It exposes exactly the
-- finite quotient operation needed by the Int8 normalization layer:
-- positive Nat denominator, Nat quotient, and Int8 storage projection.
------------------------------------------------------------------------

data PositiveNat : Set where
  positive : Nat → PositiveNat

positiveValue : PositiveNat → Nat
positiveValue (positive n) = suc n

finiteDivideNat : Nat → PositiveNat → Nat
finiteDivideNat numerator denominator =
  numerator / positiveValue denominator

finiteDivideInt8 : Int8 → PositiveNat → Int8
finiteDivideInt8 x denominator =
  int8OfNat (finiteDivideNat (toℕ (code x)) denominator)

finiteDivide-two-step :
  ∀ (x : Int8) (d : PositiveNat) →
  finiteDivideInt8 x d ≡
  int8OfNat ((toℕ (code x)) / positiveValue d)
finiteDivide-two-step x d = refl
