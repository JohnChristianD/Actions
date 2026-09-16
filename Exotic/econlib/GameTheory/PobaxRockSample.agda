{-# OPTIONS --safe #-}
module Exotic.econlib.GameTheory.PobaxRockSample where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _∸_)

-- Provenance: POBAx / JAX RockSample environment.
-- A deterministic finite kernel is used here. Observation uncertainty is
-- represented explicitly by the rock-status component rather than by an
-- implicit random source.

data Direction : Set where
  north east south west : Direction

data Action : Set where
  move : Direction → Action
  sample : Nat → Action

data RockStatus : Set where
  bad good : RockStatus

record Rock : Set where
  constructor rock
  field
    position index : Nat
    status : RockStatus

record State : Set where
  constructor state
  field
    row col : Nat
    collected : Nat

record Kernel : Set where
  constructor kernel
  field
    width height : Nat
    rockAt : Nat → Rock

step : Kernel → State → Action → State
step K s (move north) = state (State.row s ∸ 1) (State.col s) (State.collected s)
step K s (move east) = state (State.row s) (State.col s + 1) (State.collected s)
step K s (move south) = state (State.row s + 1) (State.col s) (State.collected s)
step K s (move west) = state (State.row s) (State.col s ∸ 1) (State.collected s)
step K s (sample n) with Rock.status (Kernel.rockAt K n)
... | bad = s
... | good = state (State.row s) (State.col s) (State.collected s + 1)

sampleReward : Kernel → Action → Nat
sampleReward K (sample n) with Rock.status (Kernel.rockAt K n)
... | bad = 0
... | good = 1
sampleReward K _ = 0
