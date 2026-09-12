{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.AllSafeCombined where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (toℕ)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _,_)
open import Exotic.efficient_chad.Int8
  using
    ( Int8
    ; code
    ; int8OfNat
    ; primal
    ; identityCHAD
    ; identityCHAD-law
    ; int8Roundtrip
    )
open import Exotic.econlib.GameTheory
  using
    ( Action
    ; defect
    ; prisonersDilemma
    ; PureNash
    ; pdIter
    ; pdIter-stabilises
    ; isNashEquilibriumDD
    )
open import Exotic.econlib.Equilibrium
  using
    ( Economy2
    ; canonicalEconomy2
    ; canonicalEconomy2Equilibrium
    ; WalrasianEquilibrium2
    ; clearAllocation
    ; clearIter
    ; clearIter-stabilises
    ; ProductionEconomy2
    ; WalrasianProductionEquilibrium2
    ; exists_equilibrium_prod2
    )

testInt8Identity : ∀ (x : Int8) → primal identityCHAD x ≡ x
testInt8Identity x = identityCHAD-law x

testInt8Roundtrip : ∀ (x : Int8) →
  toℕ (code (int8OfNat (toℕ (code x)))) ≡ toℕ (code x)
testInt8Roundtrip x = int8Roundtrip x

testEquilibrium : WalrasianEquilibrium2 canonicalEconomy2
testEquilibrium = canonicalEconomy2Equilibrium

testNashDD : PureNash prisonersDilemma defect defect
testNashDD = isNashEquilibriumDD

testNashConvergence : ∀ n → pdIter (suc n) (defect , defect) ≡ (defect , defect)
testNashConvergence n = pdIter-stabilises n (defect , defect)

testMarketStabilisation : ∀ n e → clearIter (suc n) e ≡ clearAllocation e
testMarketStabilisation n e = clearIter-stabilises n e

testProductionExistence : Σ ProductionEconomy2 (λ e → WalrasianProductionEquilibrium2 e)
testProductionExistence = exists_equilibrium_prod2
