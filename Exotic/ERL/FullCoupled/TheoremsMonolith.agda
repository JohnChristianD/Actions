{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TheoremsMonolith where

------------------------------------------------------------------------
-- Single active theorem source for the canonical learner.
-- Discovery/CI should target this file. Legacy theorem modules are not
-- part of the canonical proof surface.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; trans; sym)
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
-- Learner-local symbolic composition algebra.
--
-- This is the semantic target for automated program/theorem search:
-- the search program composes actual learner transformations and asks
-- the canonical Agda surface to prove the resulting observation law.
-- The search metric is deliberately absent from this semantic layer.
------------------------------------------------------------------------

data LearnerReplacement : Set where
  attentionReplacement : LearnedSparsemaxAttention → LearnerReplacement
  normReplacement : NormPair → LearnerReplacement
  optimizerReplacement : F4IntUState → LearnerReplacement

applyLearnerReplacement :
  LearnerReplacement →
  FullLearnerState →
  FullLearnerState
applyLearnerReplacement (attentionReplacement a) s =
  replaceAttention s a
applyLearnerReplacement (normReplacement n) s =
  replaceNorm s n
applyLearnerReplacement (optimizerReplacement o) s =
  replaceOptimizer s o

applyLearnerReplacements :
  List LearnerReplacement →
  FullLearnerState →
  FullLearnerState
applyLearnerReplacements [] s = s
applyLearnerReplacements (r ∷ rs) s =
  applyLearnerReplacements rs (applyLearnerReplacement r s)

canonicalPolicy-learnerReplacement-invariant :
  ∀ K s r →
  canonicalPolicy K (applyLearnerReplacement r s)
  ≡
  canonicalPolicy K s
canonicalPolicy-learnerReplacement-invariant K s
  (attentionReplacement a) =
  canonicalPolicy-attention-invariant K s a
canonicalPolicy-learnerReplacement-invariant K s
  (normReplacement n) =
  canonicalPolicy-norm-invariant K s n
canonicalPolicy-learnerReplacement-invariant K s
  (optimizerReplacement o) =
  canonicalPolicy-optimizer-invariant K s o

canonicalPolicy-learnerReplacement-composition :
  ∀ K s rs →
  canonicalPolicy K (applyLearnerReplacements rs s)
  ≡
  canonicalPolicy K s
canonicalPolicy-learnerReplacement-composition K s [] = refl
canonicalPolicy-learnerReplacement-composition K s (r ∷ rs) =
  trans
    (canonicalPolicy-learnerReplacement-composition
      K
      (applyLearnerReplacement r s)
      rs)
    (canonicalPolicy-learnerReplacement-invariant K s r)

canonicalNormPair-afterFullStep-iterate :
  ∀ K n s →
  normPairWeightPlusOne
    (norm (iterateCanonical K n s))
  ≡
  normPairWeightPlusOne (norm s)
canonicalNormPair-afterFullStep-iterate K zero s = refl
canonicalNormPair-afterFullStep-iterate K (suc n) s =
  trans
    (canonicalNormPair-afterFullStep-iterate
      K n (canonicalFullStep K s))
    (canonicalNormPairWeightPlusOne-preservation K s)

canonicalPersistentGRU-afterFullStep-iterate :
  ∀ K n s →
  persistentGRU
    (gru (iterateCanonical K n s))
  ≡
  persistentGRU (gru s)
canonicalPersistentGRU-afterFullStep-iterate K zero s = refl
canonicalPersistentGRU-afterFullStep-iterate K (suc n) s =
  trans
    (canonicalPersistentGRU-afterFullStep-iterate
      K n (canonicalFullStep K s))
    (canonicalPersistentGRUPreservation K s)

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


------------------------------------------------------------------------
-- Intrinsic endogenous attention-mediator connected theorem.
--
-- This theorem is intentionally independent of TSTS, program search,
-- evolutionary search, PVS, and JAxtar.  It is a property of the
-- executable learner itself.
--
-- An arbitrary attention-state replacement is policy-invariant and
-- therefore leaves the count and Q-log channels unchanged, but the
-- replacement enters the endogenous Watkins target.  That same target
-- is then consumed by both the GRU and F4 optimizer tells.
------------------------------------------------------------------------

record FiniteAttentionWatkinsGRUF4MediatorTheorem : Set₁ where
  constructor finiteAttentionWatkinsGRUF4MediatorTheorem
  field
    attentionPolicyInvariant :
      ∀ K s a →
      C.canonicalPolicy K (C.replaceAttention s a)
      ≡
      C.canonicalPolicy K s

    attentionCountInvariant :
      ∀ K s a →
      C.canonicalCountStep K (C.replaceAttention s a)
      ≡
      C.canonicalCountStep K s

    attentionQLogInvariant :
      ∀ K s a →
      C.canonicalQLogStep K (C.replaceAttention s a)
      ≡
      C.canonicalQLogStep K s

    attentionTargetExpansion :
      ∀ K s a →
      C.canonicalWatkinsTarget K (C.replaceAttention s a)
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
          (C.canonicalAttentionMix K (C.replaceAttention s a))
          (C.int8Add
            (C.canonicalGRUFeedback s)
            (C.int8Add
              (C.canonicalF4L2Feedback K s)
              (C.int8Add
                (C.canonicalQLogControlFeedback s)
                (C.canonicalQLogValueFeedback s)))))

    sharedTargetFeedsGRU :
      ∀ K s a →
      C.canonicalGRUStep K (C.replaceAttention s a)
      ≡
      C.gruStep
        (C.gru s)
        (C.int8Add
          (C.canonicalWatkinsTarget K (C.replaceAttention s a))
          (C.canonicalAttentionMix K (C.replaceAttention s a)))

    sharedTargetFeedsF4 :
      ∀ K s a →
      C.canonicalOptimizerStep K (C.replaceAttention s a)
      ≡
      C.f4ThetaStep
        (C.optimizerKernel K)
        (C.optimizer s)
        (C.canonicalWatkinsTarget K (C.replaceAttention s a))

    fullStepCountChannelInvariant :
      ∀ K s a →
      C.lcbCounts
        (C.canonicalFullStep K (C.replaceAttention s a))
      ≡
      C.lcbCounts
        (C.canonicalFullStep K s)

    fullStepQLogChannelInvariant :
      ∀ K s a →
      C.qLogValue
        (C.canonicalFullStep K (C.replaceAttention s a))
      ≡
      C.qLogValue
        (C.canonicalFullStep K s)

    fullStepNormPairInvariant :
      ∀ K s a →
      C.normPairWeightPlusOne
        (C.norm (C.canonicalFullStep K (C.replaceAttention s a)))
      ≡
      C.normPairWeightPlusOne (C.norm s)

    fullStepPersistentGRUInvariant :
      ∀ K s a →
      C.persistentGRU
        (C.gru (C.canonicalFullStep K (C.replaceAttention s a)))
      ≡
      C.persistentGRU (C.gru (C.replaceAttention s a))

open FiniteAttentionWatkinsGRUF4MediatorTheorem public

finite-attention-watkins-gru-f4-mediator-theorem :
  FiniteAttentionWatkinsGRUF4MediatorTheorem
finite-attention-watkins-gru-f4-mediator-theorem =
  finiteAttentionWatkinsGRUF4MediatorTheorem
    (λ K s a → C.canonicalPolicy-attention-invariant K s a)
    (λ K s a →
      refl)
    (λ K s a →
      refl)
    (λ K s a →
      refl)
    (λ K s a →
      C.canonicalRecurrentInput-law K (C.replaceAttention s a))
    (λ K s a →
      C.canonicalOptimizerStep-qMunchausen-L2 K (C.replaceAttention s a))
    (λ K s a →
      refl)
    (λ K s a →
      refl)
    (λ K s a →
      trans
        (C.canonicalNormPairWeightPlusOne-preservation
          K
          (C.replaceAttention s a))
        refl)
    (λ K s a →
      C.canonicalPersistentGRUPreservation
        K
        (C.replaceAttention s a))


------------------------------------------------------------------------
-- Compact novel theorem basis for the canonical learner.
--
-- These four laws are the minimal nontrivial representatives retained by
-- the Mercury symbolic quotient.  They are compositional consequences of
-- the canonical learner laws, not bare definitional-reflexivity candidates.
------------------------------------------------------------------------

novel-clockPlus4-endogenousFeedback-invariant :
  ∀ K s →
  C.canonicalEndogenousFeedback K
    (replaceClock s
      (suc (suc (suc (suc (C.clock s))))))
  ≡
  C.canonicalEndogenousFeedback K s
novel-clockPlus4-endogenousFeedback-invariant K s =
  cong
    (λ x →
      C.int8Add
        x
        (C.int8Add
          (C.canonicalGRUFeedback s)
          (C.int8Add
            (C.canonicalF4L2Feedback K s)
            (C.int8Add
              (C.canonicalQLogControlFeedback s)
              (C.canonicalQLogValueFeedback s)))))
    (canonicalAttentionMix-clock-period4 K s)

record NovelLearnerTheoremBasis : Set₁ where
  constructor novelLearnerTheoremBasis
  field
    normReplacementCountStep :
      ∀ K s n →
      C.canonicalCountStep K (C.replaceNorm s n)
      ≡
      C.canonicalCountStep K s

    normReplacementQLogStep :
      ∀ K s n →
      C.canonicalQLogStep K (C.replaceNorm s n)
      ≡
      C.canonicalQLogStep K s

    clockPlus4EndogenousFeedback :
      ∀ K s →
      C.canonicalEndogenousFeedback K
        (replaceClock s
          (suc (suc (suc (suc (C.clock s))))))
      ≡
      C.canonicalEndogenousFeedback K s

    clockPlus4WatkinsTarget :
      ∀ K s →
      C.canonicalWatkinsTarget K
        (replaceClock s
          (suc (suc (suc (suc (C.clock s))))))
      ≡
      C.canonicalWatkinsTarget K s

open NovelLearnerTheoremBasis public

novel-learner-theorem-basis :
  NovelLearnerTheoremBasis
novel-learner-theorem-basis =
  novelLearnerTheoremBasis
    (λ K s n →
      cong₂ C.updateLCBCount
        (canonicalPolicy-norm-invariant K s n)
        refl)
    (λ K s n →
      cong
        (λ p → C.negativeFiniteQLog8 (C.policyLeftWeight p))
        (canonicalPolicy-norm-invariant K s n))
    novel-clockPlus4-endogenousFeedback-invariant
    (λ K s →
      trans
        (C.canonicalWatkinsTarget-law K
          (replaceClock s
            (suc (suc (suc (suc (C.clock s)))))))
        (cong
          (λ x →
            C.int8Add
              (C.int8Add
                (C.int8Add
                  (C.canonicalReward8 K s)
                  (C.canonicalQLogBias K s))
                (C.int8Mul
                  C.canonicalDiscount8
                  (C.maxCriticValue8 (C.critic (C.watkins s)))))
              x)
          (novel-clockPlus4-endogenousFeedback-invariant K s)))


------------------------------------------------------------------------
-- Exact recurrent scan class.
--
-- No finite horizon is baked into this theorem. The input is a Nat-indexed
-- stream, and the prefix/split laws quantify over arbitrary natural
-- horizons. The associativity is over endomorphism composition, so the
-- recurrent state transition itself is not approximated or relaxed.
------------------------------------------------------------------------

record RecurrentAssociativeScanTheorem
  (State Input : Set) : Set₁ where
  constructor recurrentAssociativeScanTheorem
  field
    actionAssociative :
      ∀ (f g h : C.Endomorphism State) s →
      C.applyEndomorphism
        (C.composeEndomorphism
          (C.composeEndomorphism f g)
          h)
        s
      ≡
      C.applyEndomorphism
        (C.composeEndomorphism
          f
          (C.composeEndomorphism g h))
        s

    prefixCorrect :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs : Nat → Input)
        (n : Nat)
        (s : State) →
      C.applyEndomorphism
        (C.recurrentPrefixEndomorphism R xs n)
        s
      ≡
      C.recurrentPrefixState R xs n s

    prefixSplit :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs : Nat → Input)
        (m n : Nat)
        (s : State) →
      C.recurrentPrefixState R xs (m + n) s
      ≡
      C.recurrentPrefixState
        R
        (C.shiftInput xs m)
        n
        (C.recurrentPrefixState R xs m s)

canonicalGRU-recurrent-associative-scan-theorem :
  RecurrentAssociativeScanTheorem C.GRUState C.Int8
canonicalGRU-recurrent-associative-scan-theorem =
  recurrentAssociativeScanTheorem
    C.endomorphismAssociative
    C.recurrentPrefix-correct
    C.recurrentPrefix-split

------------------------------------------------------------------------
-- Finite exact reservoir-faithfulness class.
--
-- This is the exact finite/discrete form of the left-inverse implication:
-- a reservoir observation with a verified left inverse is injective and
-- every target on the hidden state factors exactly through that observation.
------------------------------------------------------------------------

record FiniteReservoirFaithfulnessTheorem
  (State Output : Set)
  (observe : State → Output) : Set₁ where
  constructor finiteReservoirFaithfulnessTheorem
  field
    inverse : Output → State
    leftInverse :
      ∀ s → inverse (observe s) ≡ s

    injective :
      ∀ {s t} →
      observe s ≡ observe t →
      s ≡ t

    exactReadout :
      ∀ {Y : Set} (target : State → Y) s →
      (λ o → target (inverse o)) (observe s)
      ≡
      target s

finiteReservoirFaithfulnessTheorem :
  ∀ {State Output : Set}
  (observe : State → Output)
  (inverse : Output → State)
  (leftInverse : ∀ s → inverse (observe s) ≡ s) →
  FiniteReservoirFaithfulnessTheorem State Output observe
finiteReservoirFaithfulnessTheorem
  observe inverse leftInverse =
  finiteReservoirFaithfulnessTheorem
    observe
    inverse
    leftInverse
    (λ {s} {t} eq →
      trans
        (sym (leftInverse s))
        (trans
          (cong inverse eq)
          (leftInverse t)))
    (λ target s →
      cong target (leftInverse s))


------------------------------------------------------------------------
-- Explicit equality-composition theorem.
--
-- The e-graph proof-plan combinator is dependency composition.  Actual
-- equality composition is represented separately by composeEqualityTheorem,
-- whose proof term uses trans.  A reflexive identity is never used as the
-- composition theorem itself.
------------------------------------------------------------------------

record EqualityCompositionTheorem
  {A : Set}
  {x y z : A} : Set where
  constructor equalityCompositionTheorem
  field
    firstStep : x ≡ y
    secondStep : y ≡ z
    composedStep : x ≡ z

composeEqualityTheorem :
  ∀ {A : Set} {x y z : A} →
  x ≡ y →
  y ≡ z →
  EqualityCompositionTheorem
composeEqualityTheorem first second =
  equalityCompositionTheorem
    first
    second
    (trans first second)

------------------------------------------------------------------------
-- E-graph completed theorem package.
--
-- Mercury selects a dependency-composed proof plan for each class.  This
-- record collects the exact Agda theorem objects that the selected plans
-- must close.  The e-graph is not a second proof checker: Agda remains the
-- authority for the final terms.
------------------------------------------------------------------------

record EGraphCompletedTheoremBasis : Set₁ where
  constructor eGraphCompletedTheoremBasis
  field
    novelBasis :
      NovelLearnerTheoremBasis

    policyReplacementComposition :
      ∀ K s rs →
      C.canonicalPolicy K (applyLearnerReplacements rs s)
      ≡
      C.canonicalPolicy K s

    equalityComposition :
      ∀ {A : Set} {x y z : A}
      → x ≡ y
      → y ≡ z
      → x ≡ z

    attentionMediator :
      FiniteAttentionWatkinsGRUF4MediatorTheorem

    recurrentScan :
      RecurrentAssociativeScanTheorem C.GRUState C.Int8

    finiteReservoir :
      FiniteReservoirFaithfulnessTheorem
        C.Int8
        C.Int8
        (λ x → x)

    noUnboundedInt8Memory :
      ∀ (f : Nat → C.Int8) →
      ¬ (∀ {m n} → f m ≡ f n → m ≡ n)

open EGraphCompletedTheoremBasis public

egraph-completed-theorem-basis :
  EGraphCompletedTheoremBasis
egraph-completed-theorem-basis =
  eGraphCompletedTheoremBasis
    novel-learner-theorem-basis
    canonicalPolicy-learnerReplacement-composition
    (λ {A} {x} {y} {z} first second →
      EqualityCompositionTheorem.composedStep
        (composeEqualityTheorem first second))
    finite-attention-watkins-gru-f4-mediator-theorem
    canonicalGRU-recurrent-associative-scan-theorem
    (finiteReservoirFaithfulnessTheorem
      (λ x → x)
      (λ x → x)
      (λ x → refl))
    C.int8-no-countably-unbounded-injective
