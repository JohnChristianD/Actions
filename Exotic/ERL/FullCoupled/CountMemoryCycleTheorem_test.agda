{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CountMemoryCycleTheorem_test where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_<_; z≤n; s≤s)
open import Exotic.ERL.FullCoupled.CountMemoryCycleTheorem

record TwoState : Set where
  constructor twoState
  field
    countNat : Nat
open TwoState public

stepUp : TwoState → TwoState
stepUp s = twoState (suc (countNat s))

natLessSucc : ∀ n → n < suc n
natLessSucc zero = s≤s z≤n
natLessSucc (suc n) = s≤s (natLessSucc n)

strictUp : StrictCountSystem TwoState stepUp
strictUp = strictCountSystem
  countNat
  (λ s nf → natLessSucc (countNat s))
