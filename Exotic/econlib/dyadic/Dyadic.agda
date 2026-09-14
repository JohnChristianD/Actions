{-# OPTIONS --safe #-}
module Exotic.econlib.dyadic.Dyadic where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Integer using (Integer; _+_; _*_; -_; _≤_)
open import Data.Fin using (toℕ)
open import Exotic.efficient_chad.Int8 using (Int8; code)

------------------------------------------------------------------------
-- Dyadic rationals only.
-- A value is an integer numerator divided by a power of two.  The
-- representation is intentionally not generalized to arbitrary rationals.
------------------------------------------------------------------------

pow2 : Nat → Integer
pow2 zero = 1
pow2 (suc n) = pow2 n * 2

record Dyadic : Set where
  constructor dyadic
  field
    numerator : Integer
    exponent : Nat

open Dyadic public

zeroᵈ : Dyadic
zeroᵈ = dyadic 0 0

oneᵈ : Dyadic
oneᵈ = dyadic 1 0

negᵈ : Dyadic → Dyadic
negᵈ (dyadic n e) = dyadic (- n) e

_+ᵈ_ : Dyadic → Dyadic → Dyadic
_+ᵈ_ (dyadic n₁ e₁) (dyadic n₂ e₂) =
  dyadic (n₁ * pow2 e₂ + n₂ * pow2 e₁) (e₁ + e₂)

_*ᵈ_ : Dyadic → Dyadic → Dyadic
_*ᵈ_ (dyadic n₁ e₁) (dyadic n₂ e₂) =
  dyadic (n₁ * n₂) (e₁ + e₂)

_≤ᵈ_ : Dyadic → Dyadic → Set
_≤ᵈ_ (dyadic n₁ e₁) (dyadic n₂ e₂) =
  n₁ * pow2 e₂ ≤ n₂ * pow2 e₁

------------------------------------------------------------------------
-- Fixed-denominator embedding of the existing finite Int8 carrier.
------------------------------------------------------------------------

int8AsDyadic : Int8 → Dyadic
int8AsDyadic x = dyadic (toInteger (toℕ (code x))) 8
  where
  toInteger : Nat → Integer
  toInteger zero = 0
  toInteger (suc n) = toInteger n + 1
