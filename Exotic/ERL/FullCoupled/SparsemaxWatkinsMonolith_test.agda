{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SparsemaxWatkinsMonolith_test where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.SparsemaxWatkinsMonolith

sparsemax-left-test :
  sparsemax2Weights (actionScore (int8OfNat 2) (int8OfNat 1))
    ≡ (oneWeight , zeroWeight)
sparsemax-left-test = refl

sparsemax-right-test :
  sparsemax2Weights (actionScore (int8OfNat 1) (int8OfNat 2))
    ≡ (zeroWeight , oneWeight)
sparsemax-right-test = refl

sparsemax-tie-test :
  sparsemax2Weights (actionScore (int8OfNat 2) (int8OfNat 2))
    ≡ (halfWeight , halfWeight)
sparsemax-tie-test = refl

monolith-endogenous-test :
  ∀ {A : F4Scalar} (K : FullCoupledKernel A) →
  fullStep K (canonicalInitialState {A = A})
    ≡ fullCoupledState
        (suc zero)
        (coupledCriticStep K (canonicalInitialState {A = A}))
        (coupledGRUStep K (canonicalInitialState {A = A}))
        (coupledOptimizerStep K (canonicalInitialState {A = A}))
        (norm (canonicalInitialState {A = A}))
        (coupledCountStep K (canonicalInitialState {A = A}))
        (qLogControl (canonicalInitialState {A = A}))
monolith-endogenous-test K =
  fullStep-endogenous K (canonicalInitialState {A = _})

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
