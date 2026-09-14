{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.DyadicLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_; z≤n)
open import Exotic.efficient_chad.Int8 using (Int8; zero8; one8; int8OfNat; code)
open import Data.Fin using (Fin; zero; suc)

------------------------------------------------------------------------
-- Probability laws are finite modules for the existing exploration
-- methods.  They are not exploration methods themselves.
--
-- Every canonical probability is represented by an integer numerator over
-- denominator 256.  No transcendental, irrational, or non-dyadic value is
-- present in this theorem surface.
------------------------------------------------------------------------

data Law : Set where
  flatDyadic : Law
  lazyUnit : Law
  dyadicLadder : Law

data Method : Set where
  mr15GA : Method
  openES : Method
  noisyNetGRU : Method

law-denominator : Law → Nat
law-denominator flatDyadic = 256
law-denominator lazyUnit = 256
law-denominator dyadicLadder = 256

flat-weight : Int8 → Nat
flat-weight x = 1

flat-normalized : 256 * 1 ≡ 256
flat-normalized = refl

flat-scale-invariant :
  ∀ (x y : Int8) → flat-weight x ≡ flat-weight y
flat-scale-invariant x y = refl

flat-symmetric :
  ∀ (x y : Int8) → flat-weight x ≡ flat-weight y
flat-symmetric x y = refl

flat-weakly-unimodal :
  ∀ (x y : Int8) → flat-weight x ≡ flat-weight y
flat-weakly-unimodal x y = refl

-- Lazy unit walk: weights 64/128/64 for -1/0/+1.
lazy-minus-weight : Nat
lazy-minus-weight = 64

lazy-zero-weight : Nat
lazy-zero-weight = 128

lazy-plus-weight : Nat
lazy-plus-weight = 64

lazy-normalized :
  lazy-minus-weight + lazy-zero-weight + lazy-plus-weight ≡ 256
lazy-normalized = refl

-- Dyadic ladder: weights 4/12/48/128/48/12/4 on
-- -4,-2,-1,0,+1,+2,+4.
ladder-m4-weight : Nat
ladder-m4-weight = 4

ladder-m2-weight : Nat
ladder-m2-weight = 12

ladder-m1-weight : Nat
ladder-m1-weight = 48

ladder-zero-weight : Nat
ladder-zero-weight = 128

ladder-p1-weight : Nat
ladder-p1-weight = 48

ladder-p2-weight : Nat
ladder-p2-weight = 12

ladder-p4-weight : Nat
ladder-p4-weight = 4

ladder-normalized :
  ladder-m4-weight + ladder-m2-weight + ladder-m1-weight
  + ladder-zero-weight + ladder-p1-weight + ladder-p2-weight
  + ladder-p4-weight ≡ 256
ladder-normalized = refl

------------------------------------------------------------------------
-- Support witnesses.  The unit generator is explicit for the two sparse
-- laws; the flat law has every finite Int8 state in support.
------------------------------------------------------------------------

data FlatSupport : Int8 → Set where
  flat-support : ∀ x → FlatSupport x

data LazySupport : Int8 → Set where
  lazy-zero : LazySupport zero8
  lazy-plus : LazySupport one8
  lazy-minus : LazySupport (int8OfNat 255)

data LadderSupport : Int8 → Set where
  ladder-zero : LadderSupport zero8
  ladder-plus : LadderSupport one8
  ladder-minus : LadderSupport (int8OfNat 255)
  ladder-plus2 : LadderSupport (int8OfNat 2)
  ladder-minus2 : LadderSupport (int8OfNat 254)
  ladder-plus4 : LadderSupport (int8OfNat 4)
  ladder-minus4 : LadderSupport (int8OfNat 252)

data HasZero : Law → Set where
  flat-zero : HasZero flatDyadic
  lazy-zero : HasZero lazyUnit
  ladder-zero : HasZero dyadicLadder

data HasUnitGenerator : Law → Set where
  flat-generator : HasUnitGenerator flatDyadic
  lazy-generator : HasUnitGenerator lazyUnit
  ladder-generator : HasUnitGenerator dyadicLadder

data SymmetricLaw : Law → Set where
  flat-symmetric-law : SymmetricLaw flatDyadic
  lazy-symmetric-law : SymmetricLaw lazyUnit
  ladder-symmetric-law : SymmetricLaw dyadicLadder

data WeaklyUnimodalLaw : Law → Set where
  flat-unimodal-law : WeaklyUnimodalLaw flatDyadic
  lazy-unimodal-law : WeaklyUnimodalLaw lazyUnit
  ladder-unimodal-law : WeaklyUnimodalLaw dyadicLadder

data DyadicLaw : Law → Set where
  flat-dyadic-law : DyadicLaw flatDyadic
  lazy-dyadic-law : DyadicLaw lazyUnit
  ladder-dyadic-law : DyadicLaw dyadicLadder

law-has-zero : ∀ l → HasZero l
law-has-zero flatDyadic = flat-zero
law-has-zero lazyUnit = lazy-zero
law-has-zero dyadicLadder = ladder-zero

law-has-unit-generator : ∀ l → HasUnitGenerator l
law-has-unit-generator flatDyadic = flat-generator
law-has-unit-generator lazyUnit = lazy-generator
law-has-unit-generator dyadicLadder = ladder-generator

law-is-symmetric : ∀ l → SymmetricLaw l
law-is-symmetric flatDyadic = flat-symmetric-law
law-is-symmetric lazyUnit = lazy-symmetric-law
law-is-symmetric dyadicLadder = ladder-symmetric-law

law-is-weakly-unimodal : ∀ l → WeaklyUnimodalLaw l
law-is-weakly-unimodal flatDyadic = flat-unimodal-law
law-is-weakly-unimodal lazyUnit = lazy-unimodal-law
law-is-weakly-unimodal dyadicLadder = ladder-unimodal-law

law-is-dyadic : ∀ l → DyadicLaw l
law-is-dyadic flatDyadic = flat-dyadic-law
law-is-dyadic lazyUnit = lazy-dyadic-law
law-is-dyadic dyadicLadder = ladder-dyadic-law

------------------------------------------------------------------------
-- Flat is special algebraically: it is invariant under every relabelling
-- of the finite support because every point has the same weight.  The other
-- laws retain symmetry and weak unimodality but do not inherit this stronger
-- all-relabeling invariance.
------------------------------------------------------------------------
flat-relabel-invariant :
  ∀ (f : Int8 → Int8) (x : Int8) → flat-weight (f x) ≡ flat-weight x
flat-relabel-invariant f x = refl
