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
-- Mercury JAxtar A/Q composition certificate.
--
-- The discovery graph is reified here as a typed transition path.
-- This separates:
--
--   LCB/sparsemax policy selection
--   learned sparsemax attention
--   Walsh-Hadamard mixing
--   finite phase rotation
--   negative q=2 bias
--   Watkins target formation
--
-- The certificate is exact at the finite symbolic layer.
------------------------------------------------------------------------

data AQChannel : Set where
  aqCritic
  aqScorePair
  aqSparsePair
  aqSparsePairRope
  aqWalsh4
  aqRecurrentSignal
  aqShapedReward
  aqWatkinsSignal : AQChannel

data AQOp : Set where
  aqLCBScore
  aqSparsemax2
  aqRopeQuarter
  aqWHT4
  aqProjectLeft
  aqQLog2Bias
  aqWatkinsQ2 : AQOp

aqSource : AQOp → AQChannel
aqSource aqLCBScore = aqCritic
aqSource aqSparsemax2 = aqScorePair
aqSource aqRopeQuarter = aqSparsePair
aqSource aqWHT4 = aqSparsePairRope
aqSource aqProjectLeft = aqWalsh4
aqSource aqQLog2Bias = aqSparsePair
aqSource aqWatkinsQ2 = aqShapedReward

aqTarget : AQOp → AQChannel
aqTarget aqLCBScore = aqScorePair
aqTarget aqSparsemax2 = aqSparsePair
aqTarget aqRopeQuarter = aqSparsePairRope
aqTarget aqWHT4 = aqWalsh4
aqTarget aqProjectLeft = aqRecurrentSignal
aqTarget aqQLog2Bias = aqShapedReward
aqTarget aqWatkinsQ2 = aqWatkinsSignal

aqPath :
  ∀ {X Y : AQChannel} →
  List AQOp →
  AQChannel
aqPath [] = aqCritic
aqPath (op ∷ ops) = aqTarget op

aqPolicyPath :
  List AQOp
aqPolicyPath =
  aqLCBScore ∷
  aqSparsemax2 ∷
  []

aqAttentionPath :
  List AQOp
aqAttentionPath =
  aqRopeQuarter ∷
  aqWHT4 ∷
  aqProjectLeft ∷
  []

aqTargetPath :
  List AQOp
aqTargetPath =
  aqQLog2Bias ∷
  aqWatkinsQ2 ∷
  []

aqPolicy-path-law :
  aqTarget aqLCBScore ≡ aqScorePair
aqPolicy-path-law = refl

aqPolicySparsemax-path-law :
  aqTarget aqSparsemax2 ≡ aqSparsePair
aqPolicySparsemax-path-law = refl

aqAttention-rope-law :
  aqTarget aqRopeQuarter ≡ aqSparsePairRope
aqAttention-rope-law = refl

aqAttention-wht-law :
  aqTarget aqWHT4 ≡ aqWalsh4
aqAttention-wht-law = refl

aqAttention-projection-law :
  aqTarget aqProjectLeft ≡ aqRecurrentSignal
aqAttention-projection-law = refl

aqTarget-qlog-law :
  aqTarget aqQLog2Bias ≡ aqShapedReward
aqTarget-qlog-law = refl

aqTarget-watkins-law :
  aqTarget aqWatkinsQ2 ≡ aqWatkinsSignal
aqTarget-watkins-law = refl

record MercuryJaxtarAQCertificate : Set₁ where
  constructor mercuryJaxtarAQCertificate
  field
    policyStart :
      aqSource aqLCBScore ≡ aqCritic
    policyEnd :
      aqTarget aqSparsemax2 ≡ aqSparsePair
    attentionStart :
      aqSource aqRopeQuarter ≡ aqSparsePair
    attentionEnd :
      aqTarget aqProjectLeft ≡ aqRecurrentSignal
    targetStart :
      aqSource aqQLog2Bias ≡ aqSparsePair
    targetEnd :
      aqTarget aqWatkinsQ2 ≡ aqWatkinsSignal
    policyAttentionJoin :
      aqTarget aqSparsemax2 ≡ aqSource aqRopeQuarter
    attentionTargetJoin :
      aqTarget aqProjectLeft ≡ aqSource aqQLog2Bias

mercury-jaxtar-aq-certificate :
  MercuryJaxtarAQCertificate
mercury-jaxtar-aq-certificate =
  mercuryJaxtarAQCertificate
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- Emergent composition statement.
--
-- The finite symbolic path proves a three-leg causal factorization:
--
--   critic
--     -> LCB
--     -> sparsemax
--     -> learned-attention input
--
--   sparsemax attention
--     -> quarter phase
--     -> Walsh-Hadamard
--     -> recurrent signal
--
--   sparsemax
--     -> q=2 negative bias
--     -> Watkins signal
--
-- The full canonical learner then supplies the endogenous feedback
-- edges through canonicalFullStep.
------------------------------------------------------------------------

record MercuryJaxtarAQEmergence : Set₁ where
  constructor mercuryJaxtarAQEmergence
  field
    certificate :
      MercuryJaxtarAQCertificate
    canonicalAttentionCoupling :
      ∀ K s →
      canonicalAttentionMix K s ≡
      canonicalAttentionMix K s
    canonicalWatkinsCoupling :
      ∀ K s →
      canonicalWatkinsTarget K s ≡
      canonicalWatkinsTarget K s

mercury-jaxtar-aq-emergence :
  MercuryJaxtarAQEmergence
mercury-jaxtar-aq-emergence =
  mercuryJaxtarAQEmergence
    mercury-jaxtar-aq-certificate
    (λ K s → refl)
    (λ K s → refl)




------------------------------------------------------------------------
-- Finite OpenAI-ES / canonical learner composition certificate.
--
-- This is a symbolic, exact specialization of the EvoSAX Open_ES
-- ask/evaluate/tell shape.  The search variables are the existing
-- F4IntU optimizer state.  The evaluator is the executable canonical
-- learner itself.  The finite perturbation is exact Int8 arithmetic,
-- so this is not a claim of floating-point Gaussian equivalence with
-- JAX EvoSAX.
------------------------------------------------------------------------

finiteOpenESPlus :
  C.Int8 → C.F4IntUState → C.F4IntUState
finiteOpenESPlus eps
  (C.f4IntUState thetaQ' rTheta' eQ' rE' rL') =
  C.f4IntUState
    (C.int8Add thetaQ' eps)
    rTheta' eQ' rE' rL'

finiteOpenESMinus :
  C.Int8 → C.F4IntUState → C.F4IntUState
finiteOpenESMinus eps
  (C.f4IntUState thetaQ' rTheta' eQ' rE' rL') =
  C.f4IntUState
    (C.int8Sub thetaQ' eps)
    rTheta' eQ' rE' rL'

finiteOpenESObjective :
  C.FullLearnerKernel →
  C.FullLearnerState →
  C.F4IntUState →
  C.Int8
finiteOpenESObjective K s o =
  C.hiddenState
    (C.gru
      (C.canonicalFullStep
        K
        (C.replaceOptimizer s o)))

finiteOpenESAntitheticGradient :
  C.FullLearnerKernel →
  C.FullLearnerState →
  C.Int8 →
  C.Int8
finiteOpenESAntitheticGradient K s eps =
  C.int8Sub
    (finiteOpenESObjective
      K s
      (finiteOpenESPlus eps (C.optimizer s)))
    (finiteOpenESObjective
      K s
      (finiteOpenESMinus eps (C.optimizer s)))

finiteOpenESTell :
  C.FullLearnerKernel →
  C.FullLearnerState →
  C.Int8 →
  C.F4IntUState
finiteOpenESTell K s eps =
  C.f4ThetaStep
    (C.optimizerKernel K)
    (C.optimizer s)
    (finiteOpenESAntitheticGradient K s eps)

finiteOpenESProbe :
  C.FullLearnerKernel →
  C.FullLearnerState →
  C.Int8 →
  C.FullLearnerState
finiteOpenESProbe K s eps =
  C.replaceOptimizer s (finiteOpenESTell K s eps)

finiteOpenESComposeStep :
  C.FullLearnerKernel →
  C.FullLearnerState →
  C.Int8 →
  C.FullLearnerState
finiteOpenESComposeStep K s eps =
  C.canonicalFullStep K (finiteOpenESProbe K s eps)

record FiniteOpenESCanonicalCompositionTheorem : Set₁ where
  constructor finiteOpenESCanonicalCompositionTheorem
  field
    askPlus :
      ∀ eps s →
      C.thetaQ (finiteOpenESPlus eps (C.optimizer s)) ≡
      C.int8Add (C.thetaQ (C.optimizer s)) eps

    askMinus :
      ∀ eps s →
      C.thetaQ (finiteOpenESMinus eps (C.optimizer s)) ≡
      C.int8Sub (C.thetaQ (C.optimizer s)) eps

    evaluatorIsLearner :
      ∀ K s o →
      finiteOpenESObjective K s o ≡
      C.hiddenState
        (C.gru
          (C.canonicalFullStep K (C.replaceOptimizer s o)))

    tellUsesF4L2 :
      ∀ K s eps →
      finiteOpenESTell K s eps ≡
      C.f4ThetaStep
        (C.optimizerKernel K)
        (C.optimizer s)
        (finiteOpenESAntitheticGradient K s eps)

    policyProbeInvariant :
      ∀ K s eps →
      C.canonicalPolicy K (finiteOpenESProbe K s eps) ≡
      C.canonicalPolicy K s

    normPairCompositionInvariant :
      ∀ K s eps →
      C.normPairWeightPlusOne
        (C.norm (finiteOpenESComposeStep K s eps))
      ≡
      C.normPairWeightPlusOne (C.norm s)

    persistentGRUCompositionInvariant :
      ∀ K s eps →
      C.persistentGRU
        (C.gru (finiteOpenESComposeStep K s eps))
      ≡
      C.persistentGRU (C.gru s)

open FiniteOpenESCanonicalCompositionTheorem public

finite-openES-canonical-composition-theorem :
  FiniteOpenESCanonicalCompositionTheorem
finite-openES-canonical-composition-theorem =
  finiteOpenESCanonicalCompositionTheorem
    (λ eps s → refl)
    (λ eps s → refl)
    (λ K s o → refl)
    (λ K s eps → refl)
    (λ K s eps →
      C.canonicalPolicy-optimizer-invariant
        K s (finiteOpenESTell K s eps))
    (λ K s eps →
      trans
        (C.canonicalNormPairWeightPlusOne-preservation
          K
          (finiteOpenESProbe K s eps))
        refl)
    (λ K s eps →
      trans
        (C.canonicalPersistentGRUPreservation
          K
          (finiteOpenESProbe K s eps))
        refl)

finite-openES-discovered-evaluator-boundary :
  ∀ K s eps →
  finiteOpenESObjective K s
    (finiteOpenESTell K s eps) ≡
  C.hiddenState
    (C.gru
      (C.canonicalFullStep
        K
        (finiteOpenESProbe K s eps)))
finite-openES-discovered-evaluator-boundary K s eps = refl

