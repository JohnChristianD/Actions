{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TheoremsMonolith where

------------------------------------------------------------------------
-- Single active theorem source for the canonical learner.
-- Discovery/CI should target this file. Legacy theorem modules are not
-- part of the canonical proof surface.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Fin using (toℕ)
open import Data.Nat using (_<ᵇ_)
open import Data.List.Base using (List; []; _∷_)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C

phase4-period4 :
  ∀ n →
  C.phase4
    (suc (suc (suc (suc n))))
  ≡
  C.phase4 n
phase4-period4 n = refl

walshRademacherRope4-period4 :
  ∀ n w →
  C.walshRademacherRope4
    (suc (suc (suc (suc n))))
    w
  ≡
  C.walshRademacherRope4 n w
walshRademacherRope4-period4 n w = refl

replaceClock :
  C.FullLearnerState → Nat → C.FullLearnerState
replaceClock s n =
  C.fullLearnerState
    n
    (C.watkins s)
    (C.attention s)
    (C.gru s)
    (C.optimizer s)
    (C.norm s)
    (C.lcbCounts s)
    (C.qLogControl s)
    (C.qLogValue s)

canonicalAttentionMix-clock-period4 :
  ∀ K s →
  C.canonicalAttentionMix K
    (replaceClock s
      (suc (suc (suc (suc (C.clock s))))))
  ≡
  C.canonicalAttentionMix K s
canonicalAttentionMix-clock-period4 K s = refl

record CanonicalAQLoopTheorem : Set₁ where
  constructor canonicalAQLoopTheorem
  field
    policyComposition :
      ∀ K s →
      C.canonicalPolicy K s ≡
      C.fixedTemperatureSparsemax
        (C.lcbScore
          (C.lcbKernel K)
          (C.lcbCounts s)
          (C.critic (C.watkins s)))

    learnedAttentionComposition :
      ∀ K s →
      C.canonicalAttentionMix K s ≡
      let
        p = C.learnedSparsemaxAttentionWeights (C.attention s)
        w = C.walshHadamardApply (C.liftAttention p)
      in
      C.int8Add
        (C.attentionToGRU K w)
        (C.walshRademacherRopeReadout (C.clock s) w)

    sharedWatkinsSignal :
      ∀ K s →
      C.canonicalSignal K s ≡
      C.canonicalWatkinsTarget K s

    gruAttentionCoupling :
      ∀ K s →
      C.canonicalGRUStep K s ≡
      C.gruStep
        (C.gru s)
        (C.int8Add
          (C.canonicalSignal K s)
          (C.canonicalAttentionMix K s))

    f4SignalCoupling :
      ∀ K s →
      C.canonicalOptimizerStep K s ≡
      C.f4ThetaStep
        (C.optimizerKernel K)
        (C.optimizer s)
        (C.canonicalSignal K s)

    watkinsEndogenousCoupling :
      ∀ K s →
      C.canonicalWatkinsTarget K s ≡
      C.int8Add
        (C.int8Add
          (C.int8Add
            (C.canonicalReward8 K s)
            (C.canonicalQLogBias K s))
          (C.int8Mul
            C.canonicalDiscount8
            (C.maxCriticValue8 (C.critic (C.watkins s)))))
        (C.canonicalEndogenousFeedback K s)

open CanonicalAQLoopTheorem public

canonical-aq-loop-theorem :
  CanonicalAQLoopTheorem
canonical-aq-loop-theorem =
  canonicalAQLoopTheorem
    (λ K s → refl)
    (λ K s → refl)
    (λ K s → refl)
    (λ K s → refl)
    (λ K s → refl)
    (λ K s → refl)

canonicalClockAfter :
  ∀ K n s →
  C.clock (C.iterateCanonical K n s) ≡ C.clock s + n
canonicalClockAfter = C.clockAfter

canonicalAperiodic :
  ∀ K s n →
  C.iterateCanonical K (suc n) s ≢ s
canonicalAperiodic = C.canonicalAperiodic

canonicalNoNontrivialFiniteCycle :
  ∀ K s n →
  C.iterateCanonical K (suc n) s ≡ s → ⊥
canonicalNoNontrivialFiniteCycle = C.canonicalNoNontrivialFiniteCycle

record CanonicalConnectedCompositionTheorem : Set₁ where
  constructor canonicalConnectedCompositionTheorem
  field
    aqLoop :
      CanonicalAQLoopTheorem
    ropePhasePeriod :
      ∀ n w →
      C.walshRademacherRope4
        (suc (suc (suc (suc n))))
        w
      ≡
      C.walshRademacherRope4 n w
    clockGrowth :
      ∀ K n s →
      C.clock (C.iterateCanonical K n s) ≡ C.clock s + n
    finiteCycleExclusion :
      ∀ K s n →
      C.iterateCanonical K (suc n) s ≡ s → ⊥

canonical-connected-composition-theorem :
  CanonicalConnectedCompositionTheorem
canonical-connected-composition-theorem =
  canonicalConnectedCompositionTheorem
    canonical-aq-loop-theorem
    walshRademacherRope4-period4
    canonicalClockAfter
    canonicalNoNontrivialFiniteCycle


------------------------------------------------------------------------
-- Finite TSTS-only endogenous connected composition.
--
-- The outer search is only Thompson Sampling Tree Search. JAxtar/A*
-- graph search and evolutionary-population proposal layers are retired
-- from the canonical discovery path.
--
-- The finite boundary exposes the TSTS role as an opaque posterior-sample
-- witness, then makes the evaluator exact:
--
--   posterior sample
--       -> selected branch
--       -> endogenous learner probe
--       -> exact Watkins target
--       -> posterior update
--       -> GRU tell + F4 tell
--
-- This is a finite semantic boundary, not a numerical reimplementation of
-- the external TSTS runtime or a claim that its Bayesian regret theorem
-- automatically transfers to this deterministic learner.
------------------------------------------------------------------------

data FiniteTSTSBranch : Set where
  tstsWatkinsBranch
  tstsF4L2Branch
  tstsGRUBranch : FiniteTSTSBranch

record FiniteTSTSPosterior : Set where
  constructor finiteTSTSPosterior
  field
    sampleWatkins
    sampleF4L2
    sampleGRU : Nat
open FiniteTSTSPosterior public

finiteTSTSBranchSample :
  FiniteTSTSPosterior →
  FiniteTSTSBranch →
  Nat
finiteTSTSBranchSample p tstsWatkinsBranch = sampleWatkins p
finiteTSTSBranchSample p tstsF4L2Branch = sampleF4L2 p
finiteTSTSBranchSample p tstsGRUBranch = sampleGRU p

finiteTSTSChoose2 :
  FiniteTSTSPosterior →
  FiniteTSTSBranch →
  FiniteTSTSBranch →
  FiniteTSTSBranch
finiteTSTSChoose2 p a b
  with finiteTSTSBranchSample p a <ᵇ finiteTSTSBranchSample p b
... | true = b
... | false = a

finiteTSTSSelect :
  FiniteTSTSPosterior →
  FiniteTSTSBranch
finiteTSTSSelect p =
  finiteTSTSChoose2
    p
    (finiteTSTSChoose2 p tstsWatkinsBranch tstsF4L2Branch)
    tstsGRUBranch

finiteTSTSProbe :
  C.FullLearnerKernel →
  FiniteTSTSBranch →
  C.Int8 →
  C.FullLearnerState →
  C.FullLearnerState
finiteTSTSProbe K tstsWatkinsBranch d s =
  C.fullLearnerState
    (C.clock s)
    (C.watkinsState
      (C.critic (C.watkins s))
      (C.int8Add (C.signal (C.watkins s)) d)
      (C.trace (C.watkins s)))
    (C.attention s)
    (C.gru s)
    (C.optimizer s)
    (C.norm s)
    (C.lcbCounts s)
    (C.qLogControl s)
    (C.qLogValue s)
finiteTSTSProbe K tstsF4L2Branch d s =
  C.replaceOptimizer s
    (C.f4ThetaStep
      (C.optimizerKernel K)
      (C.optimizer s)
      d)
finiteTSTSProbe K tstsGRUBranch d s =
  C.fullLearnerState
    (C.clock s)
    (C.watkins s)
    (C.attention s)
    (C.gruStep (C.gru s) d)
    (C.optimizer s)
    (C.norm s)
    (C.lcbCounts s)
    (C.qLogControl s)
    (C.qLogValue s)

finiteTSTSSelectedBranch :
  FiniteTSTSPosterior →
  FiniteTSTSBranch
finiteTSTSSelectedBranch p = finiteTSTSSelect p

finiteTSTSSelectedProbe :
  C.FullLearnerKernel →
  FiniteTSTSPosterior →
  C.Int8 →
  C.FullLearnerState →
  C.FullLearnerState
finiteTSTSSelectedProbe K p d s =
  finiteTSTSProbe K (finiteTSTSSelectedBranch p) d s

finiteTSTSSelectedTarget :
  C.FullLearnerKernel →
  FiniteTSTSPosterior →
  C.Int8 →
  C.FullLearnerState →
  C.Int8
finiteTSTSSelectedTarget K p d s =
  C.canonicalWatkinsTarget K
    (finiteTSTSSelectedProbe K p d s)

finiteTSTSReward :
  C.FullLearnerKernel →
  FiniteTSTSPosterior →
  C.Int8 →
  C.FullLearnerState →
  Nat
finiteTSTSReward K p d s =
  toℕ (C.code (finiteTSTSSelectedTarget K p d s))

finiteTSTSPosteriorUpdate :
  FiniteTSTSPosterior →
  FiniteTSTSBranch →
  Nat →
  FiniteTSTSPosterior
finiteTSTSPosteriorUpdate p tstsWatkinsBranch r =
  finiteTSTSPosterior
    (sampleWatkins p + r)
    (sampleF4L2 p)
    (sampleGRU p)
finiteTSTSPosteriorUpdate p tstsF4L2Branch r =
  finiteTSTSPosterior
    (sampleWatkins p)
    (sampleF4L2 p + r)
    (sampleGRU p)
finiteTSTSPosteriorUpdate p tstsGRUBranch r =
  finiteTSTSPosterior
    (sampleWatkins p)
    (sampleF4L2 p)
    (sampleGRU p + r)

finiteTSTSNextPosterior :
  C.FullLearnerKernel →
  FiniteTSTSPosterior →
  C.Int8 →
  C.FullLearnerState →
  FiniteTSTSPosterior
finiteTSTSNextPosterior K p d s =
  finiteTSTSPosteriorUpdate
    p
    (finiteTSTSSelectedBranch p)
    (finiteTSTSReward K p d s)

finiteTSTSClosedStep :
  C.FullLearnerKernel →
  FiniteTSTSPosterior →
  C.Int8 →
  C.FullLearnerState →
  C.FullLearnerState
finiteTSTSClosedStep K p d s =
  C.canonicalFullStep K
    (finiteTSTSSelectedProbe K p d s)

record FiniteTSTSEndogenousConnectedTheorem : Set₁ where
  constructor finiteTSTSEndogenousConnectedTheorem
  field
    selectedTarget-law :
      ∀ K p d s →
      finiteTSTSSelectedTarget K p d s
      ≡
      C.canonicalWatkinsTarget K
        (finiteTSTSSelectedProbe K p d s)

    posteriorUpdateUsesEndogenousReward :
      ∀ K p d s →
      finiteTSTSBranchSample
        (finiteTSTSNextPosterior K p d s)
        (finiteTSTSSelectedBranch p)
      ≡
      finiteTSTSBranchSample p (finiteTSTSSelectedBranch p)
      + finiteTSTSReward K p d s

    selectedTargetFeedsGRU :
      ∀ K p d s →
      C.canonicalGRUStep K
        (finiteTSTSSelectedProbe K p d s)
      ≡
      C.gruStep
        (C.gru s)
        (C.int8Add
          (finiteTSTSSelectedTarget K p d s)
          (C.canonicalAttentionMix K s))

    selectedTargetFeedsF4 :
      ∀ K p d s →
      C.canonicalOptimizerStep K
        (finiteTSTSSelectedProbe K p d s)
      ≡
      C.f4ThetaStep
        (C.optimizerKernel K)
        (C.optimizer (finiteTSTSSelectedProbe K p d s))
        (finiteTSTSSelectedTarget K p d s)

    f4SelectedEndogenousExpansion :
      ∀ K p d s →
      finiteTSTSSelectedBranch p ≡ tstsF4L2Branch →
      finiteTSTSSelectedTarget K p d s
      ≡
      C.int8Add
        (C.int8Add
          (C.int8Add
            (C.canonicalReward8 K s)
            (C.canonicalQLogBias K s))
          (C.int8Mul
            C.canonicalDiscount8
            (C.maxCriticValue8 (C.critic (C.watkins s)))))
        (C.int8Add
          (C.canonicalAttentionMix K s)
          (C.int8Add
            (C.canonicalGRUFeedback s)
            (C.int8Add
              (C.int8Add
                (C.int8Add
                  (C.thetaQ (C.optimizer s))
                  d)
                (C.l2Correction
                  (C.globalL2 (C.optimizerKernel K))))
              (C.int8Add
                (C.canonicalQLogControlFeedback s)
                (C.canonicalQLogValueFeedback s)))))

    normPairPreserved :
      ∀ K p d s →
      C.normPairWeightPlusOne
        (C.norm (finiteTSTSClosedStep K p d s))
      ≡
      C.normPairWeightPlusOne (C.norm s)

    persistentGRUPreserved :
      ∀ K p d s →
      C.persistentGRU
        (C.gru (finiteTSTSClosedStep K p d s))
      ≡
      C.persistentGRU
        (C.gru (finiteTSTSSelectedProbe K p d s))

open FiniteTSTSEndogenousConnectedTheorem public

finite-tsts-endogenous-connected-theorem :
  FiniteTSTSEndogenousConnectedTheorem
finite-tsts-endogenous-connected-theorem =
  finiteTSTSEndogenousConnectedTheorem
    (λ K p d s → refl)
    (λ K p d s with finiteTSTSSelectedBranch p
     ... | tstsWatkinsBranch = refl
     ... | tstsF4L2Branch = refl
     ... | tstsGRUBranch = refl)
    (λ K p d s → refl)
    (λ K p d s → refl)
    (λ K p d s eq rewrite eq = refl)
    (λ K p d s →
      C.canonicalNormPairWeightPlusOne-preservation
        K
        (finiteTSTSSelectedProbe K p d s))
    (λ K p d s →
      C.canonicalPersistentGRUPreservation
        K
        (finiteTSTSSelectedProbe K p d s))
