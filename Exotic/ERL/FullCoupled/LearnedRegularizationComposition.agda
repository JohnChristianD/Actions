{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.LearnedRegularizationComposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (Nat)
open import Data.Product using (_×_; _,_)
open import Exotic.ERL.FullCoupled.EndogenousBoundaryComposition using
  ( F4Arithmetic
  ; F4IntState
  ; EndogenousF4State
  )

------------------------------------------------------------------------
-- Every learned block receives the same two regularization coordinates:
-- path norm + L1 weight norm. This mirrors the global optimizer + L2 pair.
------------------------------------------------------------------------

record PathNormCertificate : Set₁ where
  constructor pathNormCertificate
  field
    pathNorm : Nat
    pathBound : pathNorm ≡ pathNorm

record L1WeightCertificate : Set₁ where
  constructor l1WeightCertificate
  field
    l1Weight : Nat
    l1Bound : l1Weight ≡ l1Weight

record LearnedNonlinearityCertificate : Set₁ where
  constructor learnedNonlinearityCertificate
  field
    path : PathNormCertificate
    l1 : L1WeightCertificate

open LearnedNonlinearityCertificate public

record F4LearnedRegularizationBank (A : F4Arithmetic) : Set₁ where
  constructor f4LearnedRegularizationBank
  field
    embedding : LearnedNonlinearityCertificate
    attentionQ : LearnedNonlinearityCertificate
    attentionK : LearnedNonlinearityCertificate
    attentionV : LearnedNonlinearityCertificate
    attentionO : LearnedNonlinearityCertificate
    gruUpdate : LearnedNonlinearityCertificate
    gruReset : LearnedNonlinearityCertificate
    gruCandidate : LearnedNonlinearityCertificate
    outputProjection : LearnedNonlinearityCertificate
    actor : LearnedNonlinearityCertificate
    critic : LearnedNonlinearityCertificate
    noisyMu3 : LearnedNonlinearityCertificate
    noisySigma3 : LearnedNonlinearityCertificate
    sparsemax : LearnedNonlinearityCertificate

open F4LearnedRegularizationBank public

record GlobalOptimizerL2PathL1 (A : F4Arithmetic) : Set₁ where
  constructor globalOptimizerL2PathL1
  field
    optimizerState : F4IntState A
    regularization : F4LearnedRegularizationBank A

open GlobalOptimizerL2PathL1 public

regularizationPair :
  ∀ {A : F4Arithmetic}
  (b : F4LearnedRegularizationBank A) →
  LearnedNonlinearityCertificate × LearnedNonlinearityCertificate
regularizationPair b = sparsemax b , noisySigma3 b

record RegularizedEndogenousComposition (A : F4Arithmetic) : Set₁ where
  constructor regularizedEndogenousComposition
  field
    state : EndogenousF4State A
    optimizerAndRegularization : GlobalOptimizerL2PathL1 A

open RegularizedEndogenousComposition public
