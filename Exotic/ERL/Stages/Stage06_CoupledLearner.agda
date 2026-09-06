{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage06_CoupledLearner where

open import Agda.Builtin.Nat using (Nat; _+_; _*_; _∸_)
open import Agda.Builtin.Equality using (_≡_; refl)

record CoupledState : Set where
  constructor coupled
  field
    critic representation l2 : Nat

coupledPenalty : CoupledState → Nat
coupledPenalty s = CoupledState.l2 s * (CoupledState.critic s + CoupledState.representation s)

coupledStep : CoupledState → CoupledState
coupledStep s = coupled
  (CoupledState.critic s ∸ CoupledState.l2 s)
  (CoupledState.representation s ∸ CoupledState.l2 s)
  (CoupledState.l2 s)

coupledStepSameL2 : ∀ s → CoupledState.l2 (coupledStep s) ≡ CoupledState.l2 s
coupledStepSameL2 s = refl
