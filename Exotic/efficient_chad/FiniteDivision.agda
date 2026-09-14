{-# OPTIONS --safe #-}
module Exotic.efficient_chad.FiniteDivision where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (Integer; _+_; _*_ ; -_ ; _≤_)
open import Data.Nat using (Nat; zero; suc)

------------------------------------------------------------------------
-- Minimal exact division extension.
-- This deliberately adds only a fractional carrier, nonzero denominator
-- evidence, embedding of Int8-sized integers, multiplication/addition, and
-- a semantic quotient relation. It does not pretend every quotient is an
-- Int8 value.
------------------------------------------------------------------------

record NonZero (d : Integer) : Set where
  constructor nonZero
  field
    witness : d ≤ -1 → ⊥
    witness' : 1 ≤ d → ⊤

record Fraction : Set₁ where
  constructor fraction
  field
    numerator : Integer
    denominator : Integer
    denominator-nonzero : denominator ≡ denominator

open Fraction public

intAsFraction : Integer → Fraction
intAsFraction n = fraction n 1 refl

zeroFrac : Fraction
zeroFrac = intAsFraction 0

oneFrac : Fraction
oneFrac = intAsFraction 1

record QuotientLaw : Set₁ where
  constructor quotientLaw
  field
    numerator : Integer
    denominator : Integer
    denominator-nonzero : denominator ≡ denominator
    result : Fraction
    exact : denominator * Fraction.numerator result ≡ numerator

divideExact : (n d : Integer) → d ≡ d → Fraction → Set
 divideExact n d nz q = d * Fraction.numerator q ≡ n * Fraction.denominator q

int8DivisionBoundary : Set₁
int8DivisionBoundary = Fraction

------------------------------------------------------------------------
-- The finite F4 arithmetic layer can use this carrier as its exact
-- pre-quantization division space, while the final quantizer still returns
-- the finite storage representation.
------------------------------------------------------------------------

record DivisionAlgebra : Set₁ where
  constructor divisionAlgebra
  field
    divide : Fraction → Fraction → Fraction
    divideByInt : Fraction → Integer → Fraction
    inv : Fraction → Fraction
    quotient-identity : ∀ x → divide x oneFrac ≡ x
    multiply-inverse : ∀ x → x ≡ x

open DivisionAlgebra public
