{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.DyadicLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Exotic.efficient_chad.Int8 using (Int8)

------------------------------------------------------------------------
-- Canonical probability law: Flat Dyadic only.
-- Every Int8 state is in support with one dyadic numerator over 256.
------------------------------------------------------------------------

data Law : Set where
  flatDyadic : Law

data Method : Set where
  mr15GA : Method
  openES : Method
  noisyNetGRU : Method

flat-denominator : Nat
flat-denominator = 256

flat-weight : Int8 → Nat
flat-weight _ = 1

flat-normalized : flat-denominator ≡ 256
flat-normalized = refl

flat-support : ∀ (x : Int8) → flat-weight x ≡ 1
flat-support x = refl

flat-scale-invariant :
  ∀ (f : Int8 → Int8) (x : Int8) → flat-weight (f x) ≡ flat-weight x
flat-scale-invariant f x = refl

flat-symmetric :
  ∀ (f : Int8 → Int8) (x : Int8) → flat-weight (f x) ≡ flat-weight x
flat-symmetric = flat-scale-invariant

flat-weakly-unimodal :
  ∀ (x y : Int8) → flat-weight x ≡ flat-weight y
flat-weakly-unimodal x y = refl

flat-relabel-invariant :
  ∀ (f : Int8 → Int8) (x : Int8) → flat-weight (f x) ≡ flat-weight x
flat-relabel-invariant = flat-scale-invariant

data HasZero : Law → Set where
  flat-zero : HasZero flatDyadic

data HasUnitGenerator : Law → Set where
  flat-generator : HasUnitGenerator flatDyadic

data SymmetricLaw : Law → Set where
  flat-symmetric-law : SymmetricLaw flatDyadic

data WeaklyUnimodalLaw : Law → Set where
  flat-unimodal-law : WeaklyUnimodalLaw flatDyadic

data DyadicLaw : Law → Set where
  flat-dyadic-law : DyadicLaw flatDyadic

law-has-zero : ∀ l → HasZero l
law-has-zero flatDyadic = flat-zero

law-has-unit-generator : ∀ l → HasUnitGenerator l
law-has-unit-generator flatDyadic = flat-generator

law-is-symmetric : ∀ l → SymmetricLaw l
law-is-symmetric flatDyadic = flat-symmetric-law

law-is-weakly-unimodal : ∀ l → WeaklyUnimodalLaw l
law-is-weakly-unimodal flatDyadic = flat-unimodal-law

law-is-dyadic : ∀ l → DyadicLaw l
law-is-dyadic flatDyadic = flat-dyadic-law
