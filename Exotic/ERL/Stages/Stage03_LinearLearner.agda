{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage03_LinearLearner where

open import Agda.Builtin.Nat using (Nat; _+_)

record LinearState : Set where
  constructor state
  field
    theta phi target : Nat

qValue : LinearState → Nat
qValue s = LinearState.theta s + LinearState.phi s

tdResidual : LinearState → Nat
tdResidual s = LinearState.target s + qValue s

criticStep : LinearState → LinearState
criticStep s =
  state
    (LinearState.theta s + tdResidual s)
    (LinearState.phi s)
    (LinearState.target s)
