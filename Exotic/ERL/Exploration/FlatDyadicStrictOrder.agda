{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.FlatDyadicStrictOrder where

open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; zero)
open import Data.Bool using (Bool; false; true; if_then_else_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Exotic.ERL.Exploration.FlatDyadic using
  ( FlatOutcome
  ; flat-one
  ; flat-minus-one
  ; flat-zero
  )

SupportWeight : Set
SupportWeight = FlatOutcome → ℕ

UnitSupportCondition : SupportWeight → Set
UnitSupportCondition w =
  w flat-one ≡ 1 × w flat-minus-one ≡ 1

UniversalSupportCondition : SupportWeight → Set
UniversalSupportCondition w =
  ∀ x → w x ≡ 1

record StrictlyStronger
    (A B : SupportWeight → Set) : Set₁ where
  constructor strictlyStronger
  field
    implies : ∀ {w} → A w → B w
    separatorWeight : SupportWeight
    separatorB : B separatorWeight
    separatorNotA : ¬ A separatorWeight

universalImpliesUnit :
  ∀ {w} → UniversalSupportCondition w → UnitSupportCondition w
universalImpliesUnit universal =
  universal flat-one , universal flat-minus-one

isUnitCode : ℕ → Bool
isUnitCode 1 = true
isUnitCode 255 = true
isUnitCode _ = false

unitOnlyWeight : SupportWeight
unitOnlyWeight x = if isUnitCode (toℕ x) then 1 else 0

unitOnlyUnitSupport : UnitSupportCondition unitOnlyWeight
unitOnlyUnitSupport = refl , refl

zeroNotOne : 0 ≡ 1 → ⊥
zeroNotOne ()

unitOnlyNotUniversal :
  ¬ UniversalSupportCondition unitOnlyWeight
unitOnlyNotUniversal universal =
  zeroNotOne (universal flat-zero)

flatUniversalSupportStrictlyStrongerThanUnitSupport :
  StrictlyStronger UniversalSupportCondition UnitSupportCondition
flatUniversalSupportStrictlyStrongerThanUnitSupport =
  strictlyStronger
    universalImpliesUnit
    unitOnlyWeight
    unitOnlyUnitSupport
    unitOnlyNotUniversal
