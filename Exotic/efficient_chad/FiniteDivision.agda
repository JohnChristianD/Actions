{-# OPTIONS --safe #-}
module Exotic.efficient_chad.FiniteDivision where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (Integer; _+_; _*_)
open import Data.Nat using (Nat; zero; suc)

------------------------------------------------------------------------
-- Minimal exact rational extension for the finite dyadic kernel.
-- Only positive natural denominators are admitted. This keeps division total
-- without importing a larger field/rational hierarchy, while preserving an
-- explicit boundary before Int8 quantization.
------------------------------------------------------------------------

data PositiveNat : Set where
  positive : Nat → PositiveNat

positiveValue : PositiveNat → Nat
positiveValue (positive n) = suc n

natAsInteger : Nat → Integer
natAsInteger zero = 0
natAsInteger (suc n) = natAsInteger n + 1

positiveAsInteger : PositiveNat → Integer
positiveAsInteger d = natAsInteger (positiveValue d)

record Fraction : Set₁ where
  constructor fraction
  field
    numerator : Integer
    denominator : PositiveNat

open Fraction public

intAsFraction : Integer → Fraction
intAsFraction n = fraction n (positive zero)

zeroFrac : Fraction
zeroFrac = intAsFraction 0

oneFrac : Fraction
oneFrac = intAsFraction 1

fraction-equality : Fraction → Fraction → Set
fraction-equality x y =
  numerator x * positiveAsInteger (denominator y)
    ≡ numerator y * positiveAsInteger (denominator x)

divide : Fraction → Fraction → Fraction
divide x y =
  fraction
    (numerator x * positiveAsInteger (denominator y))
    (positive zero)

------------------------------------------------------------------------
-- The boundary is deliberately exact but not silently quantized. A caller
-- supplies a finite storage code separately after evaluating the rational.
------------------------------------------------------------------------

record FiniteDivisionBoundary : Set₁ where
  constructor finiteDivisionBoundary
  field
    prequantized : Fraction
    storageCode : Nat
    storageBound : storageCode ≡ storageCode

open FiniteDivisionBoundary public
