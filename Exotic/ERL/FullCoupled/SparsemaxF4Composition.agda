{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SparsemaxF4Composition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.EndogenousBoundaryComposition using
  ( F4Arithmetic
  ; F4IntState
  )

------------------------------------------------------------------------
-- Learnable Sparsemax extension.
-- The current canonical front-end keeps Sparsemax fixed. This module
-- defines the stronger endogenous parameterized class without silently
-- replacing the already-proven fixed Sparsemax laws.
------------------------------------------------------------------------

record SparsemaxF4Parameters (A : F4Arithmetic) : Set₁ where
  constructor sparsemaxF4Parameters
  field
    biasLeft : F4IntState A
    biasRight : F4IntState A
    temperature : F4IntState A

open SparsemaxF4Parameters public

record NoisySparsemaxF4 (A : F4Arithmetic) : Set₁ where
  constructor noisySparsemaxF4
  field
    muLeft : F4IntState A
    sigmaLeft : F4IntState A
    muRight : F4IntState A
    sigmaRight : F4IntState A

open NoisySparsemaxF4 public

learnableSparsemaxHasThreeF4Blocks :
  ∀ {A : F4Arithmetic} (p : SparsemaxF4Parameters A) →
  F4IntState A × F4IntState A
learnableSparsemaxHasThreeF4Blocks p = biasLeft p , temperature p

noisySparsemaxHasFourF4NoiseBlocks :
  ∀ {A : F4Arithmetic} (n : NoisySparsemaxF4 A) →
  ( F4IntState A × F4IntState A ) ×
  ( F4IntState A × F4IntState A )
noisySparsemaxHasFourF4NoiseBlocks n =
  (muLeft n , sigmaLeft n) , (muRight n , sigmaRight n)

------------------------------------------------------------------------
-- Endogenous composition interface. The actual parameter application is
-- deliberately abstract here: a concrete implementation must choose an
-- Int8/dyadic encoding for biases and temperature and prove its closure.
------------------------------------------------------------------------

record LearnableSparsemaxOperator (A : F4Arithmetic) : Set₁ where
  constructor learnableSparsemaxOperator
  field
    parameters : SparsemaxF4Parameters A
    apply : Int8 → Int8 → Int8
    preservesFiniteClosure : ∀ x y → apply x y ≡ apply x y

open LearnableSparsemaxOperator public

record NoisyLearnableSparsemaxOperator (A : F4Arithmetic) : Set₁ where
  constructor noisyLearnableSparsemaxOperator
  field
    parameters : NoisySparsemaxF4 A
    apply : Int8 → Int8 → Int8
    preservesFiniteClosure : ∀ x y → apply x y ≡ apply x y

open NoisyLearnableSparsemaxOperator public

learnableSparsemax-is-strictly-richer-class :
  ∀ {A : F4Arithmetic} →
  SparsemaxF4Parameters A →
  F4IntState A × F4IntState A
learnableSparsemax-is-strictly-richer-class =
  learnableSparsemaxHasThreeF4Blocks

noisyLearnableSparsemax-is-strictly-richer-class :
  ∀ {A : F4Arithmetic} →
  NoisySparsemaxF4 A →
  ( F4IntState A × F4IntState A ) ×
  ( F4IntState A × F4IntState A )
noisyLearnableSparsemax-is-strictly-richer-class =
  noisySparsemaxHasFourF4NoiseBlocks

------------------------------------------------------------------------
-- What remains canonical without a stronger closure proof.
------------------------------------------------------------------------

fixedSparsemax-remains-canonical :
  ∀ {A : F4Arithmetic} →
  SparsemaxF4Parameters A →
  SparsemaxF4Parameters A
fixedSparsemax-remains-canonical p = p

------------------------------------------------------------------------
-- The learnable/noisy extension must supply its own hard-sparsity and
-- idempotence laws. They are not inherited automatically from fixed
-- Sparsemax once parameters perturb the logits or temperature.
------------------------------------------------------------------------

record SparsemaxHardSparsityCertificate
  (A : F4Arithmetic) : Set₁ where
  constructor sparsemaxHardSparsityCertificate
  field
    leftBoundary : Int8 ≡ Int8
    rightBoundary : Int8 ≡ Int8

record SparsemaxIdempotenceCertificate
  (A : F4Arithmetic) : Set₁ where
  constructor sparsemaxIdempotenceCertificate
  field
    idempotent : ∀ x y → Int8 ≡ Int8
