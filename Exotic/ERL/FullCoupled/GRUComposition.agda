{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GRUComposition where

open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.efficient_chad.GRUGatedComposition using
  ( GRUSequentialBoundary )
open import Exotic.efficient_chad.GRURecurrentMobius using
  ( GRUWindow )
open import Exotic.ERL.FullCoupled.GRUNoisyNetState using
  ( GRUNoisyNetState )

-- Canonical representation order:
-- dyadic Walsh-Rademacher RoPE -> sparsemax -> frozen Haar -> specialized GRU.
-- No standalone pointwise activation or MLP layer is admitted here.
record SparsemaxLayer : Set₁ where
  constructor sparsemaxLayer
  field
    applySparsemax : Set → Set
    normalized : Set
    finiteSupport : Set

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

-- Only GRU and attention-side components receive the paired L1/path-one
-- obligations. The global L2 law is kept separate and coupled globally.
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

-- The repository already contains an Int8 actor/critic head boundary. The
-- finite DPG update law remains an explicit theorem obligation rather than an
-- inferred consequence of the Int8 carrier.
record Int8ActorCriticBoundary : Set₁ where
  constructor int8ActorCriticBoundary
  field
    actor : GRUNoisyNetState → Int8
    critic : GRUNoisyNetState → Int8
    actorCriticCouplingLaw : Set
    dpgUpdateLaw : Set

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
    actorCritic : Int8ActorCriticBoundary
    exactDecorrelatedFeatures : Set
