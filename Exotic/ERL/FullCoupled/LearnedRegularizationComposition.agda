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
-- Correct scope of the norm-pair: it applies only to learned nonlinearities.
-- The global optimizer/L2 coordinates remain global to every learned block.
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

record LearnedNonlinearityNormBank : Set₁ where
  constructor learnedNonlinearityNormBank
  field
    sparsemax : LearnedNonlinearityCertificate
    gruUpdate : LearnedNonlinearityCertificate
    gruReset : LearnedNonlinearityCertificate
    gruCandidate : LearnedNonlinearityCertificate

open LearnedNonlinearityNormBank public

record GlobalOptimizerL2Regularized (A : F4Arithmetic) : Set₁ where
  constructor globalOptimizerL2Regularized
  field
    optimizerState : F4IntState A
    nonlinearityNorms : LearnedNonlinearityNormBank
    learnerState : EndogenousF4State A

open GlobalOptimizerL2Regularized public

optimizerL2-is-global :
  ∀ {A : F4Arithmetic}
  (b : GlobalOptimizerL2Regularized A) →
  F4IntState A
optimizerL2-is-global b = optimizerState b

normPair-is-nonlinearity-only :
  ∀ {A : F4Arithmetic}
  (b : GlobalOptimizerL2Regularized A) →
  LearnedNonlinearityCertificate × LearnedNonlinearityCertificate
normPair-is-nonlinearity-only b =
  sparsemax (nonlinearityNorms b) , gruCandidate (nonlinearityNorms b)
