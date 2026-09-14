{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GRUComposition where

open import Agda.Builtin.Equality using (_≡_)
open import Exotic.efficient_chad.GRUGatedComposition using
  ( GRUSequentialBoundary )
open import Exotic.efficient_chad.GRURecurrentMobius using
  ( GRUWindow )

-- Architecture boundary after sparsemax: no MLP is inserted between attention
-- and the frozen Haar/GRU representation.
record SparsemaxLayer : Set₁ where
  constructor sparsemaxLayer
  field
    applySparsemax : Set → Set

record FrozenHaar2016Layer : Set₁ where
  constructor frozenHaar2016Layer
  field
    applyHaar : Set → Set
    frozen : Set
    exactDecorrelated : Set

record DyadicRoPERelation : Set₁ where
  constructor dyadicRoPERelation
  field
    applyRoPE : Set → Set
    WalshRademacherBasis : Set
    dyadicRotationLaw : Set
    frozenFeatures : Set

record NormPair : Set₁ where
  constructor normPair
  field
    l1Law : Set
    pathOneLaw : Set

record GlobalL2Regularizer : Set₁ where
  constructor globalL2Regularizer
  field
    l2Law : Set

record GlobalOptimizerBoundary : Set₁ where
  constructor globalOptimizerBoundary
  field
    optimizerLaw : Set
    globalL2Coupling : GlobalL2Regularizer
    integerF4InputLaw : Set
    softsignQIDBDLaw : Set

record GRUComposition : Set₂ where
  constructor gruComposition
  field
    sparsemax : SparsemaxLayer
    haar2016 : FrozenHaar2016Layer
    dyadicRoPE : DyadicRoPERelation
    gru : GRUSequentialBoundary
    recurrenceWindow : GRUWindow
    gruNormPair : NormPair
    sparsemaxNormPair : NormPair
    optimizer : GlobalOptimizerBoundary
    exactDecorrelatedFeatures : Set

-- The record is a theorem surface, not a data-analysis result. Every field is
-- a proof obligation or a finite operator witness supplied by the canonical
-- Agda layer; no hidden MLP or extra pointwise forward activation is admitted.
