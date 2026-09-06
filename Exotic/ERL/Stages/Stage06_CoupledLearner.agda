{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage06_CoupledLearner where

open import Agda.Builtin.Nat using (Nat; _+_; _*_; zero)
open import Agda.Builtin.Equality using (_≡_; refl)

record CoupledState : Set where
  constructor coupled
  field
    critic representation l2 : Nat

coupledPenalty : CoupledState → Nat
coupledPenalty s = CoupledState.l2 s * (CoupledState.critic s + CoupledState.representation s)

coupledStep : CoupledState → CoupledState
coupledStep s = coupled
  (CoupledState.critic s)
  (CoupledState.representation s)
  (CoupledState.l2 s)

coupledStepShape : ∀ s → coupledStep s ≡ coupledStep s
coupledStepShape s = refl

coupledStepSameL2 : ∀ s → CoupledState.l2 (coupledStep s) ≡ CoupledState.l2 s
coupledStepSameL2 s = refl

coupledPenaltyAtZeroL2 : ∀ {c r} → coupledPenalty (coupled c r zero) ≡ zero
coupledPenaltyAtZeroL2 {c} {r} = refl
