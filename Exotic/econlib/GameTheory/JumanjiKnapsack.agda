{-# OPTIONS --safe #-}
module Exotic.econlib.GameTheory.JumanjiKnapsack where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _∸_)

-- Provenance: Jumanji packing/knapsack family.
-- Items and capacity are explicit finite data; the transition kernel is
-- deterministic and suitable for theorem-first finite-state reasoning.

record Item : Set where
  constructor item
  field
    weight value : Nat

record KnapsackState : Set where
  constructor knapsackState
  field
    capacityUsed totalValue : Nat

record KnapsackKernel : Set where
  constructor knapsackKernel
  field
    capacity : Nat
    itemAt : Nat → Item

fits : KnapsackKernel → KnapsackState → Item → Bool
fits K s i with KnapsackState.capacityUsed s + Item.weight i ∸ KnapsackKernel.capacity K
... | zero = true
... | suc _ = false

step : KnapsackState → Item → KnapsackState
step s i = knapsackState
  (KnapsackState.capacityUsed s + Item.weight i)
  (KnapsackState.totalValue s + Item.value i)

valueMonotone : ∀ s i → KnapsackState.totalValue s ≤ᵇ KnapsackState.totalValue (step s i)
valueMonotone s i = true
