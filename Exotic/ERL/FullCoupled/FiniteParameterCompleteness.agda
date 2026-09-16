{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.FiniteParameterCompleteness where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_∸_; _<_; _≤_; _<ᵇ_; z≤n; s≤s)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

learnerDefaultD : Nat
learnerDefaultD = 64

data PowerOfFour : Nat → Set where
  powerOfFour-one : PowerOfFour 1
  powerOfFour-step : ∀ {d} → PowerOfFour d → PowerOfFour (d * 4)

learnerDefaultD-power4 : PowerOfFour learnerDefaultD
learnerDefaultD-power4 = powerOfFour-step (powerOfFour-step (powerOfFour-step powerOfFour-one))

record FiniteParameter (A B : Set) : Set where
  constructor finiteParameter
  field
    parameter : A → B
open FiniteParameter public

parameterize : ∀ {A B : Set} → (A → B) → FiniteParameter A B
parameterize f = finiteParameter f

parameterize-complete : ∀ {A B : Set} (f : A → B) (a : A) → parameter (parameterize f) a ≡ f a
parameterize-complete f a = refl

record FiniteIndexedParameter (n m : Nat) : Set where
  constructor finiteIndexedParameter
  field
    parameterFin : Fin n → Fin m
open FiniteIndexedParameter public

parameterizeFin : ∀ {n m : Nat} → (Fin n → Fin m) → FiniteIndexedParameter n m
parameterizeFin f = finiteIndexedParameter f

parameterizeFin-complete : ∀ {n m : Nat} (f : Fin n → Fin m) (a : Fin n) →
  parameterFin (parameterizeFin f) a ≡ f a
parameterizeFin-complete f a = refl

record FiniteStateKernel (S A O : Set) : Set₁ where
  constructor finiteStateKernel
  field
    update : S → A → S
    choose : S → A → O
open FiniteStateKernel public

finiteStateParameterComplete : ∀ {S A O : Set} (u : S → A → S) (c : S → A → O) →
  update (finiteStateKernel u c) ≡ u × choose (finiteStateKernel u c) ≡ c
finiteStateParameterComplete u c = refl , refl

finiteStateFunctionalCompleteness : ∀ {n m} (f : Fin n → Fin m) →
  parameterFin (parameterizeFin f) ≡ f
finiteStateFunctionalCompleteness f = refl
