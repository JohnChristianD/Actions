{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.FiniteParameterCompleteness where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using ()
open import Data.Nat.DivMod using ()
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

DefaultD : Nat
DefaultD = 64

data PowerOfFour : Nat → Set where
  powerOfFour-one : PowerOfFour 1
  powerOfFour-step : ∀ {d} → PowerOfFour d → PowerOfFour (d * 4)

open Agda.Builtin.Nat using (_*)

defaultD-power4 : PowerOfFour DefaultD
defaultD-power4 = powerOfFour-step (powerOfFour-step powerOfFour-step powerOfFour-one)

record FiniteParameter (A B : Set) : Set where
  constructor finiteParameter
  field
    parameter : A → B

parameterize : ∀ {A B : Set} → (A → B) → FiniteParameter A B
parameterize f = finiteParameter f

parameterize-complete : ∀ {A B : Set} (f : A → B) (a : A) → parameter (parameterize f) a ≡ f a
parameterize-complete f a = refl

record FiniteIndexedParameter (n m : Nat) : Set where
  constructor finiteIndexedParameter
  field
    parameterFin : Fin n → Fin m

parameterizeFin : ∀ {n m : Nat} → (Fin n → Fin m) → FiniteIndexedParameter n m
parameterizeFin f = finiteIndexedParameter f

parameterizeFin-complete : ∀ {n m : Nat} (f : Fin n → Fin m) (a : Fin n) → parameterFin (parameterizeFin f) a ≡ f a
parameterizeFin-complete f a = refl

record FiniteStateKernel (S A O : Set) : Set₁ where
  constructor finiteStateKernel
  field
    update : S → A → S
    choose : S → A → O

finiteStateParameterComplete : ∀ {S A O : Set} (u : S → A → S) (c : S → A → O) →
  update (finiteStateKernel u c) ≡ u × choose (finiteStateKernel u c) ≡ c
finiteStateParameterComplete u c = refl , refl

finiteStateFunctionallyComplete : ∀ {S A O : Set} (K : FiniteStateKernel S A O) →
  (update K , choose K) ≡ (update K , choose K)
finiteStateFunctionallyComplete K = refl , refl
