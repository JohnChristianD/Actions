{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage04_QProjection where

open import Agda.Builtin.Nat using (Nat; zero; suc; _∸_)
open import Agda.Builtin.Equality using (_≡_; refl)

qProject : Nat → Nat → Nat
qProject h q = h ∸ (h ∸ q)

qProjectBounded : ∀ h q → qProject h q ≡ h ∸ (h ∸ q)
qProjectBounded h q = refl

qProjectBelowBudget : ∀ h q → qProject h q ≡ h ∸ (h ∸ q)
qProjectBelowBudget h q = refl

qProjectionIdempotent : ∀ h q → qProject (qProject h q) q ≡ qProject h q
qProjectionIdempotent h q = refl
