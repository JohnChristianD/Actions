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
open import Data.Fin using (Fin; toℕ)
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
-- Generic equality composition primitive.
--
-- This is theorem algebra, not a learner-specific discovery registry.
-- Automated discovery derives its semantic vocabulary from source
-- declarations; no fixed candidate basis is encoded here.
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
-- Explicit equality-composition theorem.
--
-- The e-graph proof-plan combinator is dependency composition.  Actual
-- equality composition is represented separately by composeEqualityTheorem,
-- whose proof term uses trans.  A reflexive identity is never used as the
-- composition theorem itself.
------------------------------------------------------------------------
-- Canonical minimax/Bellman-Shapley inclusion class for the executable
-- biased Watkins + negative-q-Munchausen + L2 target.
--
-- The learner has a concrete Int8 carrier. No ordered ring, interval,
-- metric, or topology is imported here. The inclusion theorem therefore
-- takes the comparison relation and monotone minimax/Bellman-Shapley
-- operator as explicit hypotheses, while the target itself is the exact
-- executable canonicalWatkinsTarget.
------------------------------------------------------------------------

record PointwiseSandwich
  {Input Value : Set}
  (_≤_ : Value → Value → Set)
  (lower actual upper : Input → Value) : Set₁ where
  constructor pointwiseSandwich
  field
    lower≤actual : ∀ x → lower x ≤ actual x
    actual≤upper : ∀ x → actual x ≤ upper x

record MinimaxBellmanShapleyOperator
  (State Value : Set)
  (_≤_ : Value → Value → Set) : Set₁ where
  constructor minimaxBellmanShapleyOperator
  field
    value : (State → Value) → Value
    monotone :
      ∀ (f g : State → Value) →
      (∀ s → f s ≤ g s) →
      value f ≤ value g

record MinimaxBellmanShapleyInclusionTheorem
  (State Value : Set)
  (_≤_ : Value → Value → Set)
  (operator : MinimaxBellmanShapleyOperator State Value _≤_)
  (lower actual upper : State → Value) : Set₁ where
  constructor minimaxBellmanShapleyInclusionTheorem
  field
    lowerBound :
      value operator lower ≤ value operator actual
    upperBound :
      value operator actual ≤ value operator upper

open PointwiseSandwich public
open MinimaxBellmanShapleyOperator public
open MinimaxBellmanShapleyInclusionTheorem public

canonicalBiasedWatkinsNegativeQMunchausenL2Target :
  C.FullLearnerKernel → C.FullLearnerState → C.Int8
canonicalBiasedWatkinsNegativeQMunchausenL2Target =
  C.canonicalWatkinsTarget

record CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem : Set₁ where
  constructor canonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
  field
    negativeQMunchausenBias :
      ∀ x →
      C.qLog2Bias8 x ≡
      C.int8Neg
        (C.int8OfNat
          ((C.munchausenScale8 * C.numerator (C.finiteQLog8 x)) /
           C.denominator (C.finiteQLog8 x)))

    targetDecomposition :
      ∀ K s →
      canonicalBiasedWatkinsNegativeQMunchausenL2Target K s ≡
      C.int8Add
        (C.int8Add
          (C.int8Add
            (C.canonicalReward8 K s)
            (C.canonicalQLogBias K s))
          (C.int8Mul
            C.canonicalDiscount8
            (C.maxCriticValue8 (C.critic (C.watkins s)))))
        (C.canonicalEndogenousFeedback K s)

    l2ConsumesTarget :
      ∀ K s →
      C.canonicalOptimizerStep K s ≡
      C.f4ThetaStep
        (C.optimizerKernel K)
        (C.optimizer s)
        (canonicalBiasedWatkinsNegativeQMunchausenL2Target K s)

open CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem public

canonical-biased-watkins-negative-q-munchausen-l2-target-theorem :
  CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
canonical-biased-watkins-negative-q-munchausen-l2-target-theorem =
  canonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
    C.qLog2Bias8-law
    (λ K s → C.canonicalWatkinsTarget-law K s)
    (λ K s → C.canonicalOptimizerStep-qMunchausen-L2 K s)

canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class :
  ∀ (K : C.FullLearnerKernel)
  (_≤_ : C.Int8 → C.Int8 → Set)
  (operator :
    MinimaxBellmanShapleyOperator
      C.FullLearnerState
      C.Int8
      _≤_)
  (lower upper : C.FullLearnerState → C.Int8) →
  PointwiseSandwich
    _≤_
    lower
    (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
    upper →
  MinimaxBellmanShapleyInclusionTheorem
    C.FullLearnerState
    C.Int8
    _≤_
    operator
    lower
    (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
    upper
canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class
  K _≤_ operator lower upper
  (pointwiseSandwich lower≤actual actual≤upper) =
  minimaxBellmanShapleyInclusionTheorem
    (monotone operator
      lower
      (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
      lower≤actual)
    (monotone operator
      (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
      upper
      actual≤upper)

------------------------------------------------------------------------
-- Endogenous factorization through a left-invertible observation.
------------------------------------------------------------------------

canonicalWatkinsTarget-endogenous-leftInverse :
  ∀ (K : C.FullLearnerKernel)
  (observe : C.FullLearnerState → C.Int8)
  (inverse : C.Int8 → C.FullLearnerState) →
  (leftInverse : ∀ t → inverse (observe t) ≡ t) →
  ∀ s →
  C.canonicalWatkinsTarget K s ≡
    C.int8Add
      (C.int8Add
        (C.int8Add
          (C.canonicalReward8 K (inverse (observe s)))
          (C.canonicalQLogBias K (inverse (observe s))))
        (C.int8Mul
          C.canonicalDiscount8
          (C.maxCriticValue8
            (C.critic (C.watkins (inverse (observe s))))))
      (C.canonicalEndogenousFeedback K (inverse (observe s)))
canonicalWatkinsTarget-endogenous-leftInverse K observe inverse leftInverse s =
  trans
    (C.canonicalWatkinsTarget-law K s)
    (cong
      (λ t →
        C.int8Add
          (C.int8Add
            (C.int8Add
              (C.canonicalReward8 K t)
              (C.canonicalQLogBias K t))
            (C.int8Mul
              C.canonicalDiscount8
              (C.maxCriticValue8
                (C.critic (C.watkins t)))))
          (C.canonicalEndogenousFeedback K t))
      (leftInverse s))

------------------------------------------------------------------------
-- Infinite-state orbit injectivity and Nat-clock pigeonhole contradiction.
------------------------------------------------------------------------

suc-injective :
  ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

natPlus-left-cancel :
  ∀ (k m n : Nat) → k + m ≡ k + n → m ≡ n
natPlus-left-cancel zero m n eq = eq
natPlus-left-cancel (suc k) m n eq =
  natPlus-left-cancel k m n (suc-injective eq)

canonicalOrbit-state-injective :
  ∀ K s {m n : Nat} →
  C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
  m ≡ n
canonicalOrbit-state-injective K s {m} {n} eq =
  natPlus-left-cancel
    (C.clock s) m n
    (trans
      (sym (C.clockAfter K m s))
      (trans
        (cong (λ t → C.clock t) eq)
        (C.clockAfter K n s)))

-- The canonical Nat-indexed orbit is an explicit infinite-state embedding:
-- equality of orbit states forces equality of the Nat indices.
canonicalInfiniteStateOrbitEmbedding :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState) →
  ∀ {m n : Nat} →
  C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
  m ≡ n
canonicalInfiniteStateOrbitEmbedding K s =
  canonicalOrbit-state-injective K s


canonicalPigeonholeNatClockContradiction :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  (observe : C.FullLearnerState → C.Int8)
  (inverse : C.Int8 → C.FullLearnerState) →
  (∀ t → inverse (observe t) ≡ t) →
  ⊥
canonicalPigeonholeNatClockContradiction K s observe inverse leftInverse =
  C.int8-no-countably-unbounded-injective
    (λ n → observe (C.iterateCanonical K n s))
    (λ {m} {n} eq →
      canonicalOrbit-state-injective K s
        (trans
          (sym (leftInverse (C.iterateCanonical K m s)))
          (trans
            (cong inverse eq)
            (leftInverse (C.iterateCanonical K n s)))))

------------------------------------------------------------------------
-- Full discrete exact-UAP factorization.
--
-- This is the genuine universal statement available without topology:
-- every target on the discrete state factors exactly through an observation
-- that has a left inverse. No limits, density arguments, or real-valued
-- approximation metric are involved.
------------------------------------------------------------------------

record DiscreteExactUAPTheorem
  (State Feature Output : Set)
  (observe : State → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor discreteExactUAPTheorem
  field
    leftInverse :
      ∀ s → inverse (observe s) ≡ s
    exactReadout :
      (target : State → Output) →
      ∀ s →
      target s ≡ target (inverse (observe s))

open DiscreteExactUAPTheorem public

------------------------------------------------------------------------
-- Full universal exact-discrete UAP, not merely one chosen target.
--
-- Universal exact readout means every target State → Output factors
-- exactly through the observation.  Constructively, this is equivalent
-- to existence of a left inverse.  The identity target supplies the
-- converse, so this result is independent of topology or approximation
-- metrics.
------------------------------------------------------------------------

record DiscreteLeftInverseWitness
  (State Feature : Set)
  (observe : State → Feature) : Set₁ where
  constructor discreteLeftInverseWitness
  field
    inverse : Feature → State
    leftInverse :
      ∀ s → inverse (observe s) ≡ s

open DiscreteLeftInverseWitness public

record DiscreteExactUniversalUAP
  (State Feature : Set)
  (observe : State → Feature) : Set₁ where
  constructor discreteExactUniversalUAP
  field
    readout :
      {Output : Set} →
      (State → Output) →
      Feature →
      Output
    exactReadout :
      {Output : Set} →
      (target : State → Output) →
      ∀ s →
      target s ≡ readout target (observe s)

open DiscreteExactUniversalUAP public

discreteExactUniversalUAP-from-leftInverse :
  ∀ {State Feature : Set}
  {observe : State → Feature} →
  DiscreteLeftInverseWitness State Feature observe →
  DiscreteExactUniversalUAP State Feature observe
discreteExactUniversalUAP-from-leftInverse witness =
  discreteExactUniversalUAP
    (λ target f → target (inverse witness f))
    (λ target s → cong target (leftInverse witness s))

discreteExactUniversalUAP-to-leftInverse :
  ∀ {State Feature : Set}
  {observe : State → Feature} →
  DiscreteExactUniversalUAP State Feature observe →
  DiscreteLeftInverseWitness State Feature observe
discreteExactUniversalUAP-to-leftInverse universal =
  discreteLeftInverseWitness
    (readout universal (λ s → s))
    (λ s → sym (exactReadout universal (λ t → t) s))

record DiscreteExactUniversalUAPLeftInverseEquivalence
  (State Feature : Set)
  (observe : State → Feature) : Set₁ where
  constructor discreteExactUniversalUAPLeftInverseEquivalence
  field
    fromLeftInverse :
      DiscreteLeftInverseWitness State Feature observe →
      DiscreteExactUniversalUAP State Feature observe
    toLeftInverse :
      DiscreteExactUniversalUAP State Feature observe →
      DiscreteLeftInverseWitness State Feature observe

discreteExactUniversalUAP-leftInverse-equivalence :
  ∀ {State Feature : Set}
  {observe : State → Feature} →
  DiscreteExactUniversalUAPLeftInverseEquivalence State Feature observe
discreteExactUniversalUAP-leftInverse-equivalence =
  discreteExactUniversalUAPLeftInverseEquivalence
    discreteExactUniversalUAP-from-leftInverse
    discreteExactUniversalUAP-to-leftInverse

discreteLeftInverse-observe-injective :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State} →
  (∀ s → inverse (observe s) ≡ s) →
  ∀ {s t} →
  observe s ≡ observe t →
  s ≡ t
discreteLeftInverse-observe-injective leftInverse {s} {t} eq =
  trans
    (sym (leftInverse s))
    (trans
      (cong inverse eq)
      (leftInverse t))

discreteExactUAPTheorem-from-leftInverse :
  ∀ {State Feature Output : Set}
  (observe : State → Feature)
  (inverse : Feature → State)
  (leftInverse : ∀ s → inverse (observe s) ≡ s) →
  DiscreteExactUAPTheorem State Feature Output observe inverse
discreteExactUAPTheorem-from-leftInverse
  observe inverse leftInverse =
  discreteExactUAPTheorem
    leftInverse
    (λ target s → cong target (sym (leftInverse s)))

------------------------------------------------------------------------
-- Exact recurrent scan of the executable endogenous target stream.
------------------------------------------------------------------------

canonicalWatkinsTargetSignalStream :
  C.FullLearnerKernel →
  C.FullLearnerState →
  Nat →
  C.Int8
canonicalWatkinsTargetSignalStream K s n =
  C.canonicalWatkinsTarget K
    (C.iterateCanonical K n s)

canonicalWatkinsTarget-recurrent-prefix-correct :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  (n : Nat)
  (h : C.GRUState) →
  C.applyEndomorphism
    (C.recurrentPrefixEndomorphism
      C.canonicalGRURecurrentNetwork
      (canonicalWatkinsTargetSignalStream K s)
      n)
    h
  ≡
  C.recurrentPrefixState
    C.canonicalGRURecurrentNetwork
    (canonicalWatkinsTargetSignalStream K s)
    n
    h
canonicalWatkinsTarget-recurrent-prefix-correct K s n h =
  C.recurrentPrefix-correct
    C.canonicalGRURecurrentNetwork
    (canonicalWatkinsTargetSignalStream K s)
    n
    h

canonicalNoGlobalInt8DiscreteUAPOnOrbit :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  (observe : C.FullLearnerState → C.Int8)
  (inverse : C.Int8 → C.FullLearnerState)
  {Output : Set} →
  DiscreteExactUAPTheorem
    C.FullLearnerState
    C.Int8
    Output
    observe
    inverse →
  ⊥
canonicalNoGlobalInt8DiscreteUAPOnOrbit
  K s observe inverse witness =
  canonicalPigeonholeNatClockContradiction
    K
    s
    observe
    inverse
    (leftInverse witness)

canonicalNoGlobalInt8DiscreteUniversalUAPOnOrbit :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  (observe : C.FullLearnerState → C.Int8) →
  DiscreteExactUniversalUAP
    C.FullLearnerState
    C.Int8
    observe →
  ⊥
canonicalNoGlobalInt8DiscreteUniversalUAPOnOrbit
  K s observe universal =
  let
    witness = discreteExactUniversalUAP-to-leftInverse universal
  in
  canonicalPigeonholeNatClockContradiction
    K
    s
    observe
    (inverse witness)
    (leftInverse witness)

------------------------------------------------------------------------
-- Continuous left-inverse transfer.
--
-- The strict import boundary does not contain topology. Continuity is
-- therefore an explicit predicate supplied by the theorem caller.
------------------------------------------------------------------------

record ContinuousLeftInverseTheorem
  (State Feature : Set)
  (observe : State → Feature)
  (inverse : Feature → State)
  (Continuous : {A B : Set} → (A → B) → Set) : Set₁ where
  constructor continuousLeftInverseTheorem
  field
    observeContinuous : Continuous observe
    inverseContinuous : Continuous inverse
    leftInverse :
      ∀ s → inverse (observe s) ≡ s

open ContinuousLeftInverseTheorem public

continuousLeftInverse-injective :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State}
  {Continuous : {A B : Set} → (A → B) → Set} →
  ContinuousLeftInverseTheorem
    State Feature observe inverse Continuous →
  ∀ {s t} →
  observe s ≡ observe t →
  s ≡ t
continuousLeftInverse-injective witness {s} {t} eq =
  trans
    (sym (leftInverse witness s))
    (trans
      (cong inverse eq)
      (leftInverse witness t))

continuousLeftInverse-exactReadout-transfer :
  ∀ {State Feature Output : Set}
  {observe : State → Feature}
  {inverse : Feature → State}
  {Continuous : {A B : Set} → (A → B) → Set} →
  ContinuousLeftInverseTheorem
    State Feature observe inverse Continuous →
  (target : State → Output) →
  ∀ s →
  target s ≡ target (inverse (observe s))
continuousLeftInverse-exactReadout-transfer
  witness target s =
  cong target (sym (leftInverse witness s))

------------------------------------------------------------------------
-- Canonical Watkins exact AUP/UAP factorization through a continuous
-- left-invertible observation.  The result is exact equality, not a
-- metric approximation claim.
------------------------------------------------------------------------

canonicalWatkinsTarget-exactReadout-through-continuousLeftInverse :
  ∀ {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (observe : C.FullLearnerState → Feature)
  (inverse : Feature → C.FullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.FullLearnerState
      Feature
      observe
      inverse
      Continuous) →
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState) →
  C.canonicalWatkinsTarget K s ≡
  C.canonicalWatkinsTarget K (inverse (observe s))
canonicalWatkinsTarget-exactReadout-through-continuousLeftInverse
  observe inverse witness K s =
  continuousLeftInverse-exactReadout-transfer
    witness
    (C.canonicalWatkinsTarget K)
    s

canonicalWatkinsTarget-boundedUniversalExactAUP :
  ∀ {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (bound : Nat)
  (embed : Fin bound → C.FullLearnerState)
  (observe : C.FullLearnerState → Feature)
  (inverse : Feature → C.FullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.FullLearnerState
      Feature
      observe
      inverse
      Continuous) →
  ∀ (K : C.FullLearnerKernel)
  (i : Fin bound) →
  C.canonicalWatkinsTarget K (embed i) ≡
  C.canonicalWatkinsTarget K (inverse (observe (embed i)))
canonicalWatkinsTarget-boundedUniversalExactAUP
  bound embed observe inverse witness K i =
  canonicalWatkinsTarget-exactReadout-through-continuousLeftInverse
    observe
    inverse
    witness
    K
    (embed i)

------------------------------------------------------------------------
-- Bounded exact approximation/readout.
--
-- The domain is finite by construction: it is indexed by Fin bound.
-- Exact equality is the approximation relation, so no metric, limit,
-- compactness, or infinite orbit is required.  The only semantic input
-- beyond the finite index is a continuous left inverse.
------------------------------------------------------------------------

record BoundedContinuousLeftInverseExactApproximationTheorem
  (State Feature : Set)
  (observe : State → Feature)
  (inverse : Feature → State)
  (Continuous : {A B : Set} → (A → B) → Set)
  (bound : Nat)
  (embed : Fin bound → State) : Set₁ where
  constructor boundedContinuousLeftInverseExactApproximationTheorem
  field
    continuousLeftInverseWitness :
      ContinuousLeftInverseTheorem
        State
        Feature
        observe
        inverse
        Continuous

    exactReadoutOnBound :
      {Output : Set} →
      (target : State → Output) →
      (i : Fin bound) →
      target (embed i) ≡
      target (inverse (observe (embed i)))

    observationInjectiveOnBound :
      ∀ {i j : Fin bound} →
      observe (embed i) ≡ observe (embed j) →
      embed i ≡ embed j

open BoundedContinuousLeftInverseExactApproximationTheorem public

boundedContinuousLeftInverseExactApproximationTheorem-from-witness :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State}
  {Continuous : {A B : Set} → (A → B) → Set}
  (bound : Nat)
  (embed : Fin bound → State)
  (witness :
    ContinuousLeftInverseTheorem
      State
      Feature
      observe
      inverse
      Continuous) →
  BoundedContinuousLeftInverseExactApproximationTheorem
    State
    Feature
    observe
    inverse
    Continuous
    bound
    embed
boundedContinuousLeftInverseExactApproximationTheorem-from-witness
  bound embed witness =
  boundedContinuousLeftInverseExactApproximationTheorem
    witness
    (λ target i →
      continuousLeftInverse-exactReadout-transfer
        witness
        target
        (embed i))
    (λ {i} {j} eq →
      continuousLeftInverse-injective witness eq)

boundedExactApproximation-on-boundedOrbit :
  ∀ {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (bound : Nat)
  (embed : Fin bound → C.FullLearnerState)
  (observe : C.FullLearnerState → Feature)
  (inverse : Feature → C.FullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.FullLearnerState
      Feature
      observe
      inverse
      Continuous) →
  BoundedContinuousLeftInverseExactApproximationTheorem
    C.FullLearnerState
    Feature
    observe
    inverse
    Continuous
    bound
    embed
boundedExactApproximation-on-boundedOrbit
  bound embed observe inverse witness =
  boundedContinuousLeftInverseExactApproximationTheorem-from-witness
    bound
    embed
    witness

-- Named universal form: every output target factors exactly through the
-- observation on the finite bound, provided the observation has a
-- continuous left inverse. "Approximation" is exact equality here.
boundedUniversalExactApproximation-through-continuousLeftInverse :
  ∀ {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (bound : Nat)
  (embed : Fin bound → C.FullLearnerState)
  (observe : C.FullLearnerState → Feature)
  (inverse : Feature → C.FullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.FullLearnerState
      Feature
      observe
      inverse
      Continuous) →
  BoundedContinuousLeftInverseExactApproximationTheorem
    C.FullLearnerState
    Feature
    observe
    inverse
    Continuous
    bound
    embed
boundedUniversalExactApproximation-through-continuousLeftInverse
  bound embed observe inverse witness =
  boundedExactApproximation-on-boundedOrbit
    bound
    embed
    observe
    inverse
    witness


------------------------------------------------------------------------
-- Ring-state injectivity and dense-neighborhood separation interfaces.
--
-- These are explicit theorem contracts. The strict import boundary does
-- not define a topology or an ordered-ring hierarchy, so neither is hidden.
------------------------------------------------------------------------

record RingStateInjectivityTheorem (State : Set) : Set₁ where
  constructor ringStateInjectivityTheorem
  field
    ringState : Nat → State
    ringStateInjective :
      ∀ {m n} → ringState m ≡ ringState n → m ≡ n

open RingStateInjectivityTheorem public

canonicalRingStateInjective :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState) →
  RingStateInjectivityTheorem C.FullLearnerState
canonicalRingStateInjective K s =
  ringStateInjectivityTheorem
    (λ n → C.iterateCanonical K n s)
    (λ {m} {n} eq → canonicalOrbit-state-injective K s eq)

record DenseNeighborhoodSeparationTheorem
  (State Feature : Set)
  (embed : Nat → State)
  (observe : State → Feature) : Set₁ where
  constructor denseNeighborhoodSeparationTheorem
  field
    denseNeighborhoodSeparation :
      ∀ {m n} →
      observe (embed m) ≡ observe (embed n) →
      m ≡ n

open DenseNeighborhoodSeparationTheorem public

canonicalDenseNeighborhoodSeparation :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  (observe : C.FullLearnerState → C.Int8)
  (inverse : C.Int8 → C.FullLearnerState) →
  (∀ t → inverse (observe t) ≡ t) →
  DenseNeighborhoodSeparationTheorem
    C.FullLearnerState
    C.Int8
    (λ n → C.iterateCanonical K n s)
    observe
canonicalDenseNeighborhoodSeparation
  K s observe inverse leftInverse =
  denseNeighborhoodSeparationTheorem
    (λ {m} {n} eq →
      canonicalOrbit-state-injective K s
        (trans
          (sym (leftInverse (C.iterateCanonical K m s)))
          (trans
            (cong inverse eq)
            (leftInverse (C.iterateCanonical K n s)))))

------------------------------------------------------------------------
-- Strictly stronger combined theorem schema.
--
-- This is not a topological universal-approximation theorem under the
-- current imports. It is the exact composition available here:
-- target semantics + minimax/Bellman-Shapley inclusion + endogenous
-- left-inverse factorization + continuous-left-inverse transfer +
-- bounded exact approximation from the continuous left inverse + ring-state
-- injectivity + dense-neighborhood separation + Nat-clock pigeonhole
-- contradiction.
------------------------------------------------------------------------

record CanonicalEndogenousMinimaxBellmanShapleyUAPTheorem : Set₁ where
  constructor canonicalEndogenousMinimaxBellmanShapleyUAPTheorem
  field
    targetSemantics :
      CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem

    exactDiscreteUAP :
      ∀ {Feature Output : Set}
      (observe : C.FullLearnerState → Feature)
      (inverse : Feature → C.FullLearnerState) →
      (leftInverse : ∀ s → inverse (observe s) ≡ s) →
      DiscreteExactUAPTheorem
        C.FullLearnerState
        Feature
        Output
        observe
        inverse

    inclusionClass :
      ∀ (K : C.FullLearnerKernel)
      (_≤_ : C.Int8 → C.Int8 → Set)
      (operator :
        MinimaxBellmanShapleyOperator
          C.FullLearnerState
          C.Int8
          _≤_)
      (lower upper : C.FullLearnerState → C.Int8) →
      PointwiseSandwich
        _≤_
        lower
        (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
        upper →
      MinimaxBellmanShapleyInclusionTheorem
        C.FullLearnerState
        C.Int8
        _≤_
        operator
        lower
        (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
        upper

    endogenousFactorization :
      ∀ (K : C.FullLearnerKernel)
      (observe : C.FullLearnerState → C.Int8)
      (inverse : C.Int8 → C.FullLearnerState) →
      (leftInverse : ∀ t → inverse (observe t) ≡ t) →
      ∀ s →
      C.canonicalWatkinsTarget K s ≡
      C.int8Add
        (C.int8Add
          (C.int8Add
            (C.canonicalReward8 K (inverse (observe s)))
            (C.canonicalQLogBias K (inverse (observe s))))
          (C.int8Mul
            C.canonicalDiscount8
            (C.maxCriticValue8
              (C.critic (C.watkins (inverse (observe s))))))
        (C.canonicalEndogenousFeedback K (inverse (observe s)))

    targetScan :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (n : Nat)
      (h : C.GRUState) →
      C.applyEndomorphism
        (C.recurrentPrefixEndomorphism
          C.canonicalGRURecurrentNetwork
          (canonicalWatkinsTargetSignalStream K s)
          n)
        h
      ≡
      C.recurrentPrefixState
        C.canonicalGRURecurrentNetwork
        (canonicalWatkinsTargetSignalStream K s)
        n
        h

    continuousReadoutTransfer :
      ∀ {Feature Output : Set}
      {observe : C.FullLearnerState → Feature}
      {inverse : Feature → C.FullLearnerState}
      {Continuous : {A B : Set} → (A → B) → Set} →
      ContinuousLeftInverseTheorem
        C.FullLearnerState
        Feature
        observe
        inverse
        Continuous →
      (target : C.FullLearnerState → Output) →
      ∀ s →
      target s ≡ target (inverse (observe s))

    boundedExactApproximation :
      ∀ {Feature : Set}
      {Continuous : {A B : Set} → (A → B) → Set}
      (bound : Nat)
      (embed : Fin bound → C.FullLearnerState)
      (observe : C.FullLearnerState → Feature)
      (inverse : Feature → C.FullLearnerState)
      (witness :
        ContinuousLeftInverseTheorem
          C.FullLearnerState
          Feature
          observe
          inverse
          Continuous) →
      BoundedContinuousLeftInverseExactApproximationTheorem
        C.FullLearnerState
        Feature
        observe
        inverse
        Continuous
        bound
        embed

    ringStateInjection :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState) →
      RingStateInjectivityTheorem C.FullLearnerState

    infiniteStateOrbit :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState) →
      ∀ {m n : Nat} →
      C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
      m ≡ n

    denseNeighborhoodSeparation :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (observe : C.FullLearnerState → C.Int8)
      (inverse : C.Int8 → C.FullLearnerState) →
      (∀ t → inverse (observe t) ≡ t) →
      DenseNeighborhoodSeparationTheorem
        C.FullLearnerState
        C.Int8
        (λ n → C.iterateCanonical K n s)
        observe

    pigeonholeNatClockContradiction :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (observe : C.FullLearnerState → C.Int8)
      (inverse : C.Int8 → C.FullLearnerState) →
      (∀ t → inverse (observe t) ≡ t) →
      ⊥

    noGlobalInt8DiscreteUAP :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (observe : C.FullLearnerState → C.Int8)
      (inverse : C.Int8 → C.FullLearnerState)
      {Output : Set} →
      DiscreteExactUAPTheorem
        C.FullLearnerState
        C.Int8
        Output
        observe
        inverse →
      ⊥

canonical-endogenous-minimax-bellman-shapley-uap-theorem : CanonicalEndogenousMinimaxBellmanShapleyUAPTheorem
canonical-endogenous-minimax-bellman-shapley-uap-theorem =
  canonicalEndogenousMinimaxBellmanShapleyUAPTheorem
    canonical-biased-watkins-negative-q-munchausen-l2-target-theorem
    canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class
    (λ observe inverse leftInverse →
      discreteExactUAPTheorem-from-leftInverse
        observe
        inverse
        leftInverse)
    (λ K observe inverse leftInverse s →
      canonicalWatkinsTarget-endogenous-leftInverse
        K observe inverse leftInverse s)
    (λ K s n h →
      canonicalWatkinsTarget-recurrent-prefix-correct
        K s n h)
    (λ witness target s →
      continuousLeftInverse-exactReadout-transfer
        witness
        target
        s)
    boundedUniversalExactApproximation-through-continuousLeftInverse
    canonicalRingStateInjective
    canonicalInfiniteStateOrbitEmbedding
    canonicalDenseNeighborhoodSeparation
    canonicalPigeonholeNatClockContradiction
    canonicalNoGlobalInt8DiscreteUAPOnOrbit
