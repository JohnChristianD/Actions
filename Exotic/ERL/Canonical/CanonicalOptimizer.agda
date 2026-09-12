{-# OPTIONS --safe #-}

module Exotic.ERL.Canonical.CanonicalOptimizer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- One optimizer is canonical; legacy optimizers are intentionally absent.
data Optimizer : Set where
  f4IntSoftsignQProjectedIDBD : Optimizer

canonicalOptimizer : Optimizer
canonicalOptimizer = f4IntSoftsignQProjectedIDBD

-- Exploration is a tagged choice, never a product or mixture.
data ExplorationMode : Set where
  noisyNets : ExplorationMode
  mr15GA : ExplorationMode
  openES : ExplorationMode

canonicalExploration : ExplorationMode
canonicalExploration = noisyNets

-- Uniform finite precision for the canonical learner.
canonicalPrecisionBits : Nat
canonicalPrecisionBits = 8

-- The POMDP context window is dyadic; 2^4 = 16 is the default finite case.
canonicalWindowPower : Nat
canonicalWindowPower = 4

-- The representation path is explicitly dyadic and non-transcendental.
data FrozenFeature : Set where
  walshHadamard : FrozenFeature
  haar : FrozenFeature
  helmert : FrozenFeature
  dct : FrozenFeature
  dst : FrozenFeature
  dft : FrozenFeature

canonicalFrozenFeature : FrozenFeature
canonicalFrozenFeature = walshHadamard

-- Three attention scales; the architecture is a hierarchy, not a vague Transformer tag.
data AttentionScale : Set where
  local : AttentionScale
  dilated : AttentionScale
  global : AttentionScale

canonicalScales : AttentionScale
canonicalScales = local

-- A total configuration record makes the canonical choice explicit to extraction hosts.
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

-- A total finite-mode flag used by hosts to reject accidental mixed exploration.
strictSingleExploration : ExplorationMode → Bool
strictSingleExploration noisyNets = true
strictSingleExploration mr15GA = true
strictSingleExploration openES = true

-- The finite core does not assert real-valued C1 calculus. A host implements the
-- chosen softsign-q quantizer as a finite lookup/table while this module fixes the
-- canonical optimizer and exploration composition.
