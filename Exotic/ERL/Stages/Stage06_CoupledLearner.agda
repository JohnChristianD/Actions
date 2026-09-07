{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage06_CoupledLearner where

open import Agda.Builtin.Nat using (Nat; _+_; _*_; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

record CoupledState : Set where
  constructor coupled
  field
    critic representation l2 : Nat

monus : Nat → Nat → Nat
monus a zero = a
monus zero (suc b) = zero
monus (suc a) (suc b) = monus a b

coupledPenalty : CoupledState → Nat
coupledPenalty s = CoupledState.l2 s * (CoupledState.critic s + CoupledState.representation s)

coupledStep : CoupledState → CoupledState
coupledStep s = coupled
  (monus (CoupledState.critic s) (CoupledState.l2 s))
  (monus (CoupledState.representation s) (CoupledState.l2 s))
  (CoupledState.l2 s)

coupledStepSameL2 : ∀ s → CoupledState.l2 (coupledStep s) ≡ CoupledState.l2 s
coupledStepSameL2 s = refl
