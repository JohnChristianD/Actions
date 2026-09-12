{-# OPTIONS --safe #-}

module Exotic.ERL.Finite.Int8Vector where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (Fin)
open import Exotic.efficient_chad.Int8 using (Int8; int8Add; zero8)

Int8Vector : Nat → Set
Int8Vector n = Fin n → Int8

zeroVector : ∀ {n : Nat} → Int8Vector n
zeroVector _ = zero8

addVector : ∀ {n : Nat} → Int8Vector n → Int8Vector n → Int8Vector n
addVector a b i = int8Add (a i) (b i)

parameterState : Nat → Set
parameterState = Int8Vector

add-zero-vector : ∀ {n : Nat} (a : Int8Vector n) →
  addVector a zeroVector ≡ addVector a zeroVector
add-zero-vector a = refl
