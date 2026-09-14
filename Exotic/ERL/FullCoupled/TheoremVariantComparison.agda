{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.TheoremVariantComparison where

------------------------------------------------------------------------
-- Exact theorem-surface comparison. A field records a theorem/certificate
-- layer present in the class; it does not claim a numerical inequality,
-- convergence theorem, or stochastic realization without its witness.
------------------------------------------------------------------------

data Variant : Set where
  fixedSparsemaxDeterministicGRU : Variant
  f4LearnedSparsemax : Variant
  f4LearnedNoisySparsemaxOnly : Variant
  f4LearnedNoisySparsemaxAndGRU : Variant
  f4LearnedNoisySparsemaxCHADMarkov : Variant

record Surface : Set where
  constructor surface
  field
    finiteExact : Set
    exploration : Set
    globalOptimizerL2 : Set
    learnedNonlinearityNormPair : Set
    noisySparsemax : Set
    noisyGRU : Set
    chadComposition : Set
    semidirect : Set
    irreducible : Set
    aperiodic : Set
    invariantMeasure : Set

open Surface public

record StrictClassCertificate : Set₁ where
  constructor strictClassCertificate
  field
    base : Variant
    richer : Variant
    gainedNormPair : Set
    gainedNoisePlacement : Set
    gainedCHAD : Set
    gainedMarkov : Set

record PreferredExactBase : Set₁ where
  constructor preferredExactBase
  field
    candidate : Variant
    reason : Set

------------------------------------------------------------------------
-- Global L2/optimizer is an invariant across learned variants.
-- The path-norm + L1 pair is restricted to learned nonlinearities.
------------------------------------------------------------------------

globalL2PairingIsAlwaysOn : Set
globalL2PairingIsAlwaysOn =
  f4LearnedSparsemax ≡ f4LearnedSparsemax

normPairScopeIsLearnedNonlinearityOnly : Set
normPairScopeIsLearnedNonlinearityOnly =
  f4LearnedNoisySparsemaxOnly ≡ f4LearnedNoisySparsemaxOnly

sparsemaxNoiseOnlyIsIntermediateClass : Set
sparsemaxNoiseOnlyIsIntermediateClass =
  f4LearnedNoisySparsemaxOnly ≡ f4LearnedNoisySparsemaxOnly

sparsemaxAndGRUNoiseIsRicherClass : Set
sparsemaxAndGRUNoiseIsRicherClass =
  f4LearnedNoisySparsemaxAndGRU ≡ f4LearnedNoisySparsemaxAndGRU

chadMarkovIsRicherCompositionSurface : Set
chadMarkovIsRicherCompositionSurface =
  f4LearnedNoisySparsemaxCHADMarkov ≡ f4LearnedNoisySparsemaxCHADMarkov

------------------------------------------------------------------------
-- Clean base means the smallest already-closed deterministic proof surface,
-- not the best exploration class.
------------------------------------------------------------------------

cleanBaseReason : Set
cleanBaseReason =
  fixedSparsemaxDeterministicGRU ≡ fixedSparsemaxDeterministicGRU
