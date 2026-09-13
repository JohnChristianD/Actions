{-# OPTIONS --safe #-}

module Exotic.ERL.Finite.Activation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*)
open import Data.Nat using (ℕ; _∸_)
open import Data.Fin using (toℕ)
open import Data.Nat.DivMod using (_/_)
open import Data.Bool using (if_then_else_)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8; code; int8OfNat; zero8)

lessThan : ℕ → ℕ → Bool
lessThan zero zero = false
lessThan zero (suc m) = true
lessThan (suc n) zero = false
lessThan (suc n) (suc m) = lessThan n m

signedPositive : Int8 → Bool
signedPositive x = lessThan (toℕ (code x)) 128

quantizedSoftMagnitude : ℕ → ℕ
quantizedSoftMagnitude m = (127 * m) / (128 + m)

softsignQ8 : Int8 → Int8
softsignQ8 x = int8OfNat (quantizedSoftMagnitude (toℕ (code x)))

signReLUQ8 : Int8 → Int8
signReLUQ8 x = if signedPositive x
  then x
  else int8OfNat (256 ∸ quantizedSoftMagnitude (256 ∸ toℕ (code x)))

cReLU8 : Int8 → Int8
cReLU8 x = if signedPositive x then x else zero8

softsignQ8-zero : softsignQ8 zero8 ≡ zero8
softsignQ8-zero = refl

cReLU8-zero : cReLU8 zero8 ≡ zero8
cReLU8-zero = refl
