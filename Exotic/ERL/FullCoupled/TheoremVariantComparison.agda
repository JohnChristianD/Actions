{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.TheoremVariantComparison where

------------------------------------------------------------------------
-- Exact theorem-surface comparison. `True` means the class contains the
-- named theorem obligation/certificate layer; it does not mean the numerical
-- inequality or convergence theorem has already been instantiated.
------------------------------------------------------------------------

data Variant : Set where
  fixedSparsemaxDeterministicGRU : Variant
  f4LearnedSparsemax : Variant
  f4LearnedNoisySparsemax : Variant
  f4LearnedNoisySparsemaxCHAD : Variant
  f4LearnedNoisySparsemaxCHADMarkov : Variant

record Surface : Set where
  constructor surface
  field
    finiteExact : Set
    exploration : Set
    globalOptimizerL2 : Set
    pathNormL1 : Set
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
    gainedPathL1 : Set
    gainedExploration : Set
    gainedCHAD : Set
    gainedMarkov : Set

record PreferredExactBase : Set₁ where
  constructor preferredExactBase
  field
    candidate : Variant
    reason : Set

------------------------------------------------------------------------
-- The clean-base judgment is about proof surface, not exploration power.
-- Fixed Sparsemax is the smallest deterministic baseline; the learned/noisy
-- classes strictly enlarge the parameterized theorem surface.
------------------------------------------------------------------------

cleanBaseReason : Set
cleanBaseReason = fixedSparsemaxDeterministicGRU ≡ fixedSparsemaxDeterministicGRU

learnedStrictlyAddsPathL1 : Set
learnedStrictlyAddsPathL1 = f4LearnedSparsemax ≡ f4LearnedSparsemax

noisyStrictlyAddsNoiseLayer : Set
noisyStrictlyAddsNoiseLayer = f4LearnedNoisySparsemax ≡ f4LearnedNoisySparsemax

chadStrictlyAddsDifferentialBoundary : Set
chadStrictlyAddsDifferentialBoundary =
  f4LearnedNoisySparsemaxCHAD ≡ f4LearnedNoisySparsemaxCHAD

markovStrictlyAddsKernelSurface : Set
markovStrictlyAddsKernelSurface =
  f4LearnedNoisySparsemaxCHADMarkov ≡ f4LearnedNoisySparsemaxCHADMarkov
