{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GRUComposition where

open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.efficient_chad.GRUGatedComposition using
  ( GRUSequentialBoundary )
open import Exotic.efficient_chad.GRURecurrentMobius using
  ( GRUWindow )
open import Exotic.ERL.FullCoupled.GRUNoisyNetState using
  ( GRUNoisyNetState )
open import Exotic.ERL.FullCoupled.GRUDPG using
  ( GRUDPGBoundary )

-- Canonical representation order:
-- dyadic Walsh-Rademacher positional action -> sparsemax -> frozen Haar
-- -> specialized recurrent GRU.
-- There is no standalone pointwise activation or MLP representation path.
record SparsemaxLayer : Set₁ where
  constructor sparsemaxLayer
  field
    applySparsemax : Set → Set
    normalized : Set
    finiteSupport : Set
    fixed : Set

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

-- The paired L1/path-one certificate is retained only for learned GRU
-- components. Sparsemax is fixed here and therefore has no norm-pair field.
record NormPair : Set₁ where
  constructor normPair
  field
    l1Law : Set
    pathOneLaw : Set

record GlobalL2Regularizer : Set₁ where
  constructor globalL2Regularizer
  field
    l2Law : Set

-- Optimizer and L2 remain global to every learned component in the coupled
-- composition. The optimizer boundary is not localised to the GRU.
record GlobalOptimizerBoundary : Set₁ where
  constructor globalOptimizerBoundary
  field
    optimizerLaw : Set
    globalL2Coupling : GlobalL2Regularizer
    integerF4InputLaw : Set
    softsignQIDBDLaw : Set

data GRUPerturbationMethod : Set where
  gruOpenES gruMR15 gruNoisyNet : GRUPerturbationMethod

record GRUComposition : Set₂ where
  constructor gruComposition
  field
    sparsemax : SparsemaxLayer
    haar2016 : FrozenHaar2016Layer
    dyadicRoPE : DyadicRoPERelation
    gru : GRUSequentialBoundary
    recurrenceWindow : GRUWindow
    gruNormPair : NormPair
    optimizer : GlobalOptimizerBoundary
    actorCritic : GRUDPGBoundary GRUNoisyNetState
    perturbationMethod : GRUPerturbationMethod
    exactDecorrelatedFeatures : Set
