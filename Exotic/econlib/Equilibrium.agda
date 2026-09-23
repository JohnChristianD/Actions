{-# OPTIONS --safe #-}

module Exotic.econlib.Equilibrium where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer using (ℤ; +_; _+_; _*_)
open import Data.Product using (Σ; _,_)

record Int8 : Set where
  constructor int8
  field code : ℤ
open Int8 public

int8OfNat : Nat → Int8
int8OfNat n = int8 (+ n)

int8Roundtrip : ∀ n → code (int8OfNat n) ≡ + n
int8Roundtrip n = refl

record Economy2 : Set where
  constructor economy2
  field
    price endowment allocation : Int8

open Economy2 public

marketValue : Economy2 → ℤ
marketValue e = code (price e) * code (endowment e)

allocationValue : Economy2 → ℤ
allocationValue e = code (price e) * code (allocation e)

record WalrasianEquilibrium2 (e : Economy2) : Set where
  constructor walrasianEquilibrium2
  field
    marketClears : allocation e ≡ endowment e
    wealthClears : allocationValue e ≡ marketValue e

canonicalEconomy2 : Economy2
canonicalEconomy2 = economy2 (int8OfNat 1) (int8OfNat 7) (int8OfNat 7)

canonicalEconomy2Equilibrium : WalrasianEquilibrium2 canonicalEconomy2
canonicalEconomy2Equilibrium = walrasianEquilibrium2 refl refl

canonicalMarketValue : marketValue canonicalEconomy2 ≡ + 7
canonicalMarketValue = refl

clearAllocation : Economy2 → Economy2
clearAllocation e = economy2 (price e) (endowment e) (endowment e)

clearAllocationEquilibrium : ∀ e → WalrasianEquilibrium2 (clearAllocation e)
clearAllocationEquilibrium e = walrasianEquilibrium2 refl refl

clearIter : Nat → Economy2 → Economy2
clearIter zero e = e
clearIter (suc n) e = clearIter n (clearAllocation e)

clearIter-stabilises : ∀ n e → clearIter (suc n) e ≡ clearAllocation e
clearIter-stabilises zero e = refl
clearIter-stabilises (suc n) e = clearIter-stabilises n (clearAllocation e)

record ProductionEconomy2 : Set where
  constructor productionEconomy2
  field
    price endowment supply demand : Int8

open ProductionEconomy2 public

record WalrasianProductionEquilibrium2 (e : ProductionEconomy2) : Set where
  constructor walrasianProductionEquilibrium2
  field
    marketClears : demand e ≡ supply e
    endowmentSupported : supply e ≡ endowment e
    priceFixed : price e ≡ price e

canonicalProductionEconomy2 : ProductionEconomy2
canonicalProductionEconomy2 = productionEconomy2
  (int8OfNat 1)
  (int8OfNat 7)
  (int8OfNat 7)
  (int8OfNat 7)

canonicalProductionEquilibrium2 : WalrasianProductionEquilibrium2 canonicalProductionEconomy2
canonicalProductionEquilibrium2 = walrasianProductionEquilibrium2 refl refl refl

exists_equilibrium_prod2 : Σ ProductionEconomy2 (λ e → WalrasianProductionEquilibrium2 e)
exists_equilibrium_prod2 = canonicalProductionEconomy2 , canonicalProductionEquilibrium2
