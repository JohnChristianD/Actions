{-# OPTIONS --safe #-}
module Exotic.efficient_chad.FiniteDivision where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (toℕ)
open import Data.Nat using (Nat; zero; suc; _*_) 
open import Data.Nat.DivMod using (_/_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8OfNat
  )

------------------------------------------------------------------------
-- Minimal finite division layer.
-- Only the operations needed by finite nonnegative normalization are added:
-- a positive denominator, Nat quotient, and an Int8 storage projection.
-- No general rational/field hierarchy is imported.
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

record Fraction : Set₁ where
  constructor fraction
  field
    numerator : Nat
    denominator : PositiveNat

open Fraction public

fraction-equality : Fraction → Fraction → Set
fraction-equality x y =
  numerator x * positiveValue (denominator y)
  ≡ numerator y * positiveValue (denominator x)

int8AsFraction : Int8 → Fraction
int8AsFraction x = fraction (toℕ (code x)) (positive zero)

fractional-division-code :
  ∀ (x : Int8) (d : PositiveNat) →
  finiteDivideInt8 x d ≡
  int8OfNat ((toℕ (code x)) / positiveValue d)
fractional-division-code = finiteDivide-two-step
