{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage04_QProjection where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

cong : ∀ {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

minNat : Nat → Nat → Nat
minNat zero _ = zero
minNat (suc _) zero = zero
minNat (suc h) (suc q) = suc (minNat h q)

qProject : Nat → Nat → Nat
qProject h q = minNat h q

qProjectShape : ∀ h q → qProject h q ≡ minNat h q
qProjectShape h q = refl

qProjectionIdempotent : ∀ h q → qProject (qProject h q) q ≡ qProject h q
qProjectionIdempotent zero q = refl
qProjectionIdempotent (suc h) zero = refl
qProjectionIdempotent (suc h) (suc q) = cong suc (qProjectionIdempotent h q)
