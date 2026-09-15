{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SparsemaxWatkinsMonolith_test where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.SparsemaxWatkinsMonolith

monolith-no-cycle-test :
  ∀ {A : F4Scalar} (K : FullCoupledKernel A) →
  iterateFull K (suc zero) (canonicalInitialState {A = A})
    ≢ canonicalInitialState {A = A}
monolith-no-cycle-test K =
  fullCoupledAperiodicity K (canonicalInitialState {A = _}) zero

monolith-no-cycle-absurd :
  ∀ {A : F4Scalar} (K : FullCoupledKernel A) →
  iterateFull K (suc zero) (canonicalInitialState {A = A})
    ≡ canonicalInitialState {A = A} → ⊥
monolith-no-cycle-absurd K =
  fullCoupledNoNontrivialFiniteCycle K zero
