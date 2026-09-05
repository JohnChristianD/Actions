{-# OPTIONS --safe #-}
module QClosurePredictive_v147 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

positive : Nat → Nat
positive n = n

weighted : Nat → Nat → Nat
weighted h x = h * x

project : Nat → Nat → Nat → Nat
project budget h x with weighted h x
... | y = ifLess y budget
  where
  ifLess : Nat → Nat → Nat
  ifLess zero _ = zero
  ifLess (suc n) zero = zero
  ifLess (suc n) (suc m) = suc (ifLess n m)

oracleIdentity : ∀ n → positive n ≡ n
oracleIdentity n = refl
