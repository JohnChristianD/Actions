{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TheoremsMonolith.Part1 where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (NonZero; _∸_; _<_; _≤_; _<ᵇ_; _/_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n; ℕ→Fin-notInjective)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C

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

canonicalAperiodic-theorem :
  ∀ K s n →
  C.iterateCanonical K (suc n) s ≢ s
canonicalAperiodic-theorem = C.canonicalAperiodic

canonicalNoNontrivialFiniteCycle-theorem :
  ∀ K s n →
  C.iterateCanonical K (suc n) s ≡ s → ⊥
canonicalNoNontrivialFiniteCycle-theorem = C.canonicalNoNontrivialFiniteCycle

------------------------------------------------------------------------
-- Exact finite-time composition of the canonical orbit.
------------------------------------------------------------------------

canonicalIterateComposition :
  ∀ (K : C.FullLearnerKernel)
  (m n : Nat)
  (s : C.FullLearnerState) →
  C.iterateCanonical K (m + n) s ≡
  C.iterateCanonical K n (C.iterateCanonical K m s)
canonicalIterateComposition K m zero s
  rewrite +-identityʳ m = refl
canonicalIterateComposition K m (suc n) s
  rewrite +-suc m n =
  cong (C.canonicalFullStep K)
    (canonicalIterateComposition K m n s)

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

walshRademacherRope4-period4 :
  ∀ n w →
  C.walshRademacherRope4
    (suc (suc (suc (suc n))))
    w
  ≡
  C.walshRademacherRope4 n w
walshRademacherRope4-period4 n w = refl

canonical-connected-composition-theorem :
  CanonicalConnectedCompositionTheorem
canonical-connected-composition-theorem =
  canonicalConnectedCompositionTheorem
    canonical-aq-loop-theorem
    walshRademacherRope4-period4
    canonicalClockAfter
    canonicalNoNontrivialFiniteCycle-theorem



------------------------------------------------------------------------
-- Finite TSTS-only endogenous connected composition.
--
-- The outer search is only Thompson Sampling Tree Search. JAxtar/A*
-- graph search and population-proposal layers are retired
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
  tstsWatkinsBranch : FiniteTSTSBranch
  tstsF4L2Branch : FiniteTSTSBranch
  tstsGRUBranch : FiniteTSTSBranch

record FiniteTSTSPosterior : Set where
  constructor finiteTSTSPosterior
  field
    sampleWatkins : Nat
    sampleF4L2 : Nat
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

finiteTSTSPosteriorUpdate-law :
  ∀ K p d s →
  finiteTSTSBranchSample
    (finiteTSTSNextPosterior K p d s)
    (finiteTSTSSelectedBranch p)
  ≡
  finiteTSTSBranchSample p (finiteTSTSSelectedBranch p)
  + finiteTSTSReward K p d s
finiteTSTSPosteriorUpdate-law K p d s with finiteTSTSSelectedBranch p
... | tstsWatkinsBranch = refl
... | tstsF4L2Branch = refl
... | tstsGRUBranch = refl

finiteTSTS-f4SelectedEndogenousExpansion :
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
finiteTSTS-f4SelectedEndogenousExpansion K p d s eq rewrite eq = refl

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
    finiteTSTSPosteriorUpdate-law
    (λ K p d s → refl)
    (λ K p d s → refl)
    finiteTSTS-f4SelectedEndogenousExpansion
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
-- program search, PVS, and JAxtar.  It is a property of the
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


