{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage03_LinearLearner where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _∸_)
open import Agda.Builtin.Equality using (_≡_; refl)

record LinearState : Set where
  constructor state
  field
    theta phi target : Nat

qValue : LinearState → Nat
qValue s = LinearState.theta s * LinearState.phi s

tdResidual : LinearState → Nat
tdResidual s = LinearState.target s ∸ qValue s

criticStep : LinearState → LinearState
criticStep s =
  state
    (LinearState.theta s + tdResidual s * LinearState.phi s)
    (LinearState.phi s)
    (LinearState.target s)

criticStepFixedPoint : ∀ {s} → tdResidual s ≡ zero → criticStep s ≡ s
criticStepFixedPoint {s} refl = refl
