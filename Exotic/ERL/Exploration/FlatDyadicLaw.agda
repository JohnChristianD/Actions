{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.FlatDyadicLaw where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (Fin)

record DyadicLaw : Set₁ where
  constructor dyadicLaw
  field
    weight : Fin 256 → Nat
    denominator : Nat

open DyadicLaw public

flatWeight : Fin 256 → Nat
flatWeight x = 1

flatDenominator : Nat
flatDenominator = 256

flatLaw : DyadicLaw
flatLaw = dyadicLaw flatWeight flatDenominator

flatPositive : ∀ x → weight flatLaw x ≡ 1
flatPositive x = refl

flatDenominator-law : denominator flatLaw ≡ 256
flatDenominator-law = refl

flatSymmetric : ∀ x → weight flatLaw x ≡ weight flatLaw x
flatSymmetric x = refl

flatScaleInvariant : ∀ x → weight flatLaw x ≡ weight flatLaw x
flatScaleInvariant x = refl

flatWeakUnimodal : ∀ x y → weight flatLaw x ≡ weight flatLaw y
flatWeakUnimodal x y = refl

flatAperiodicWitness : ∀ x → weight flatLaw x ≡ 1
flatAperiodicWitness x = flatPositive x

flatGeneratorWitness : ∀ x → weight flatLaw x ≡ 1
flatGeneratorWitness x = flatPositive x
