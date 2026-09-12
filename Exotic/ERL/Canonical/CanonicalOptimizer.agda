{-# OPTIONS --safe #-}

module Exotic.ERL.Canonical.CanonicalOptimizer where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)

data Optimizer : Set where
  f4IntSoftsignQProjectedIDBD : Optimizer

canonicalOptimizer : Optimizer
canonicalOptimizer = f4IntSoftsignQProjectedIDBD

data ExplorationMode : Set where
  noisyNets : ExplorationMode
  mr15GA : ExplorationMode
  openES : ExplorationMode

canonicalExploration : ExplorationMode
canonicalExploration = noisyNets

canonicalPrecisionBits : Nat
canonicalPrecisionBits = 8

canonicalWindowPower : Nat
canonicalWindowPower = 4

data FrozenFeature : Set where
  walshHadamard : FrozenFeature
  haar : FrozenFeature
  helmert : FrozenFeature
  dct : FrozenFeature
  dst : FrozenFeature
  dft : FrozenFeature

canonicalFrozenFeature : FrozenFeature
canonicalFrozenFeature = walshHadamard

data AttentionScale : Set where
  local : AttentionScale
  dilated : AttentionScale
  global : AttentionScale

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

strictSingleExploration : ExplorationMode → Bool
strictSingleExploration noisyNets = true
strictSingleExploration mr15GA = true
strictSingleExploration openES = true
