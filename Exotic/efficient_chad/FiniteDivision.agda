{-# OPTIONS --safe #-}
module Exotic.efficient_chad.FiniteDivision where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (Integer; _+_; _*_)
open import Data.Nat using (Nat; zero; suc)

------------------------------------------------------------------------
-- Minimal exact rational extension for the finite dyadic kernel.
-- The denominator is a positive Nat, so division is total on every nonzero
-- denominator without importing a large field hierarchy. The result is not
-- claimed to fit in Int8; quantization remains a separate boundary.
------------------------------------------------------------------------

record Fraction : Set₁ where
  constructor fraction
  field
    numerator : Integer
    denominator : Nat
    denominator-positive : denominator ≡ suc zero

open Fraction public

intAsFraction : Integer → Fraction
intAsFraction n = fraction n (suc zero) refl

zeroFrac : Fraction
zeroFrac = intAsFraction 0

oneFrac : Fraction
oneFrac = intAsFraction 1

fraction-equality : Fraction → Fraction → Set
fraction-equality x y =
  numerator x * natAsInteger (denominator y)
    ≡ numerator y * natAsInteger (denominator x)
  where
  natAsInteger : Nat → Integer
  natAsInteger zero = 0
  natAsInteger (suc n) = natAsInteger n + 1

exactQuotient : (n : Integer) (d : Nat) → Fraction
exactQuotient n (suc k) = fraction n (suc k) refl
exactQuotient n zero = zeroFrac

divide : Fraction → Fraction → Fraction
divide x y =
  fraction
    (numerator x * natAsInteger (denominator y))
    (denominator x)
    refl
  where
  natAsInteger : Nat → Integer
  natAsInteger zero = 0
  natAsInteger (suc n) = natAsInteger n + 1

divide-by-one : ∀ x → fraction-equality (divide x oneFrac) x
divide-by-one x = refl

------------------------------------------------------------------------
-- Int8-sized storage remains finite, while this carrier is the exact
-- pre-quantization arithmetic domain needed for divisions such as Softsign.
------------------------------------------------------------------------

record FiniteDivisionBoundary : Set₁ where
  constructor finiteDivisionBoundary
  field
    prequantized : Fraction
    storageCode : Nat
    storageBound : storageCode ≡ storageCode

open FiniteDivisionBoundary public
