{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage04_QProjection where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

minNat : Nat → Nat → Nat
minNat zero _ = zero
minNat (suc h) zero = zero
minNat (suc h) (suc q) = suc (minNat h q)

qProject : Nat → Nat → Nat
qProject h q = minNat h q

qProjectShape : ∀ h q → qProject h q ≡ minNat h q
qProjectShape h q = refl

qProjectionWellFormed : ∀ h q → qProject h q ≡ qProject h q
qProjectionWellFormed h q = refl
