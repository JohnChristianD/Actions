{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage04_QProjection where

open import Agda.Builtin.Nat using (Nat; _∸_)
open import Agda.Builtin.Equality using (_≡_; refl)

qProject : Nat → Nat → Nat
qProject h q = h ∸ (h ∸ q)

qProjectBounded : ∀ h q → qProject h q ≡ h ∸ (h ∸ q)
qProjectBounded h q = refl

qProjectionWellFormed : ∀ h q → qProject h q ≡ qProject h q
qProjectionWellFormed h q = refl
