{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.AllSafeCombined where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _,_)
open import Exotic.efficient_chad.Int8
  using
    ( Int8
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

testInt8Identity : ∀ (x : Int8) → identityCHAD-law x
testInt8Identity x = identityCHAD-law x

testInt8Roundtrip : ∀ (x : Int8) → int8Roundtrip x
testInt8Roundtrip x = int8Roundtrip x

testEquilibrium : WalrasianEquilibrium2 canonicalEconomy2
testEquilibrium = canonicalEconomy2Equilibrium

testNashDD : PureNash prisonersDilemma defect defect
testNashDD = isNashEquilibriumDD

testNashConvergence : ∀ n (a b : Action) →
  pdIter (suc n) (a , b) ≡ (defect , defect)
testNashConvergence n a b = pdIter-stabilises n (a , b)

testMarketStabilisation : ∀ n (e : Economy2) →
  clearIter (suc n) e ≡ clearAllocation e
testMarketStabilisation n e = clearIter-stabilises n e

testProductionExistence : Σ ProductionEconomy2 (λ e → WalrasianProductionEquilibrium2 e)
testProductionExistence = exists_equilibrium_prod2
