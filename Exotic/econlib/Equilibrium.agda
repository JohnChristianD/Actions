{-# OPTIONS --safe #-}

module Exotic.econlib.Equilibrium where

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; _*)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8; int8OfNat; code)

record Economy2 : Set where
  constructor economy2
  field
    price endowment allocation : Int8

open Economy2 public

marketValue : Economy2 → ℕ
marketValue e = toℕ (code (price e)) * toℕ (code (endowment e))

allocationValue : Economy2 → ℕ
allocationValue e = toℕ (code (price e)) * toℕ (code (allocation e))

record WalrasianEquilibrium2 (e : Economy2) : Set where
  constructor walrasianEquilibrium2
  field
    marketClears : allocation e ≡ endowment e
    wealthClears : allocationValue e ≡ marketValue e

canonicalEconomy2 : Economy2
canonicalEconomy2 = economy2 (int8OfNat 1) (int8OfNat 7) (int8OfNat 7)

canonicalEconomy2Equilibrium : WalrasianEquilibrium2 canonicalEconomy2
canonicalEconomy2Equilibrium = walrasianEquilibrium2 refl refl

clearAllocation : Economy2 → Economy2
clearAllocation e = economy2 (price e) (endowment e) (endowment e)

clearAllocationEquilibrium : ∀ e → WalrasianEquilibrium2 (clearAllocation e)
clearAllocationEquilibrium e = walrasianEquilibrium2 refl refl

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

canonicalProductionEconomy2 : ProductionEconomy2
canonicalProductionEconomy2 = productionEconomy2
  (int8OfNat 1)
  (int8OfNat 7)
  (int8OfNat 7)
  (int8OfNat 7)

canonicalProductionEquilibrium2 : WalrasianProductionEquilibrium2 canonicalProductionEconomy2
canonicalProductionEquilibrium2 = walrasianProductionEquilibrium2 refl refl

exists_equilibrium_prod2 : Σ ProductionEconomy2 (λ e → WalrasianProductionEquilibrium2 e)
exists_equilibrium_prod2 = canonicalProductionEconomy2 , canonicalProductionEquilibrium2
