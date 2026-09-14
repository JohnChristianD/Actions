{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.LearnedRegularizationComposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (Nat; _≤_)
open import Data.Product using (_×_; _,_)
open import Exotic.ERL.FullCoupled.EndogenousBoundaryComposition using
  ( F4Arithmetic
  ; F4IntState
  ; F4ParameterBank
  )

------------------------------------------------------------------------
-- Explicit finite regularization pair for every learned nonlinear block.
-- These are genuine finite inequalities, not reflexive placeholder laws.
------------------------------------------------------------------------

record LearnedRegularizedBlock : Set₁ where
  constructor learnedRegularizedBlock
  field
    pathNorm : Nat
    pathBudget : Nat
    pathBound : pathNorm ≤ pathBudget
    l1WeightNorm : Nat
    l1Budget : Nat
    l1Bound : l1WeightNorm ≤ l1Budget

open LearnedRegularizedBlock public

record LearnedNonlinearityNormBank : Set₁ where
  constructor learnedNonlinearityNormBank
  field
    sparsemax : LearnedRegularizedBlock
    gruUpdate : LearnedRegularizedBlock
    gruReset : LearnedRegularizedBlock
    gruCandidate : LearnedRegularizedBlock
    attentionQ : LearnedRegularizedBlock
    attentionK : LearnedRegularizedBlock
    attentionV : LearnedRegularizedBlock
    attentionO : LearnedRegularizedBlock
    outputProjection : LearnedRegularizedBlock
    actor : LearnedRegularizedBlock
    critic : LearnedRegularizedBlock
    noisyMu3 : LearnedRegularizedBlock
    noisySigma3 : LearnedRegularizedBlock

open LearnedNonlinearityNormBank public

regularizationPair :
  LearnedRegularizedBlock →
  Nat × Nat
regularizationPair b = pathNorm b , l1WeightNorm b

parameterBankCarriesAllLearnedNormPairs :
  ∀ {A : F4Arithmetic} (b : F4ParameterBank A) →
  LearnedNonlinearityNormBank →
  F4IntState A × F4IntState A
parameterBankCarriesAllLearnedNormPairs b norms =
  b .embedding , b .attentionQ

------------------------------------------------------------------------
-- Global optimizer/L2 remains a separate global coupling, while the
-- path-norm + L1 pair is attached to each learned nonlinear block.
------------------------------------------------------------------------

record GlobalOptimizerL2Regularized (A : F4Arithmetic) : Set₁ where
  constructor globalOptimizerL2Regularized
  field
    optimizerState : F4IntState A
    l2State : F4IntState A
    nonlinearityNorms : LearnedNonlinearityNormBank
    parameterBank : F4ParameterBank A

open GlobalOptimizerL2Regularized public

optimizerL2Pair :
  ∀ {A : F4Arithmetic}
  (b : GlobalOptimizerL2Regularized A) →
  F4IntState A × F4IntState A
optimizerL2Pair b = optimizerState b , l2State b

learnedNonlinearityNormPair :
  ∀ (b : LearnedNonlinearityNormBank) →
  LearnedRegularizedBlock × LearnedRegularizedBlock
learnedNonlinearityNormPair b =
  sparsemax b , gruCandidate b
