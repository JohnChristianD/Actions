{-# OPTIONS --safe #-}

module Exotic.ERL.Canonical.CanonicalOptimizer where

open import Agda.Builtin.Nat using (Nat)

data Optimizer : Set where
  standardTDLambdaInt8 : Optimizer

canonicalOptimizer : Optimizer
canonicalOptimizer = standardTDLambdaInt8

data ExplorationMode : Set where
  modifiedDyadicMR15GA : ExplorationMode

canonicalExploration : ExplorationMode
canonicalExploration = modifiedDyadicMR15GA

canonicalPrecisionBits : Nat
canonicalPrecisionBits = 8

canonicalWindowPower : Nat
canonicalWindowPower = 4

data FrozenFeature : Set where
  haar : FrozenFeature

canonicalFrozenFeature : FrozenFeature
canonicalFrozenFeature = haar

data AttentionScale : Set where
  local : AttentionScale

canonicalScales : AttentionScale
canonicalScales = local

record CanonicalConfig : Set where
  constructor canonicalConfig
  field
    optimizer : Optimizer
    exploration : ExplorationMode
    precisionBits : Nat
    windowPower : Nat
    frozenFeature : FrozenFeature

canonical : CanonicalConfig
canonical = canonicalConfig
  canonicalOptimizer
  canonicalExploration
  canonicalPrecisionBits
  canonicalWindowPower
  canonicalFrozenFeature
