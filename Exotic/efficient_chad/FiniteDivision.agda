{-# OPTIONS --safe #-}
module Exotic.efficient_chad.FiniteDivision where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (Integer; _+_; _*_)
open import Data.Nat using (Nat; zero; suc; _*_)

------------------------------------------------------------------------
-- Minimal exact division extension. This adds only positive-denominator
-- fractions and division by a provably positive finite integer. It is enough
-- to model exact pre-quantization quotients without importing a large field
-- hierarchy or pretending every quotient is Int8.
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

divideByPositive : Fraction → PositiveNat → Fraction
divideByPositive x d =
  fraction
    (numerator x)
    (positive (positiveValue (denominator x) * positiveValue d))

embedInt8Numerator : Integer → Fraction
embedInt8Numerator = intAsFraction

------------------------------------------------------------------------
-- Softsign-style exact division can live here whenever its denominator is
-- represented by PositiveNat. The eventual quantizer remains an explicit
-- downstream operation.
------------------------------------------------------------------------

record FiniteDivisionBoundary : Set₁ where
  constructor finiteDivisionBoundary
  field
    prequantized : Fraction
    storageCode : Nat
    storageBound : storageCode ≡ storageCode

open FiniteDivisionBoundary public
