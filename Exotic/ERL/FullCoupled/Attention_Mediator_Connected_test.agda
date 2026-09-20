{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.Attention_Mediator_Connected_test where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith

attention-mediator-policy-test :
  ∀ K s a →
  C.canonicalPolicy K (C.replaceAttention s a)
  ≡
  C.canonicalPolicy K s
attention-mediator-policy-test =
  FiniteAttentionWatkinsGRUF4MediatorTheorem.attentionPolicyInvariant
    finite-attention-watkins-gru-f4-mediator-theorem

attention-mediator-count-test :
  ∀ K s a →
  C.canonicalCountStep K (C.replaceAttention s a)
  ≡
  C.canonicalCountStep K s
attention-mediator-count-test =
  FiniteAttentionWatkinsGRUF4MediatorTheorem.attentionCountInvariant
    finite-attention-watkins-gru-f4-mediator-theorem

attention-mediator-qlog-test :
  ∀ K s a →
  C.canonicalQLogStep K (C.replaceAttention s a)
  ≡
  C.canonicalQLogStep K s
attention-mediator-qlog-test =
  FiniteAttentionWatkinsGRUF4MediatorTheorem.attentionQLogInvariant
    finite-attention-watkins-gru-f4-mediator-theorem

attention-mediator-target-test :
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
            (C.canonicalQLogValueFeedback s))))
attention-mediator-target-test =
  FiniteAttentionWatkinsGRUF4MediatorTheorem.attentionTargetExpansion
    finite-attention-watkins-gru-f4-mediator-theorem

attention-mediator-shared-gru-test :
  ∀ K s a →
  C.canonicalGRUStep K (C.replaceAttention s a)
  ≡
  C.gruStep
    (C.gru s)
    (C.int8Add
      (C.canonicalWatkinsTarget K (C.replaceAttention s a))
      (C.canonicalAttentionMix K (C.replaceAttention s a)))
attention-mediator-shared-gru-test =
  FiniteAttentionWatkinsGRUF4MediatorTheorem.sharedTargetFeedsGRU
    finite-attention-watkins-gru-f4-mediator-theorem

attention-mediator-shared-f4-test :
  ∀ K s a →
  C.canonicalOptimizerStep K (C.replaceAttention s a)
  ≡
  C.f4ThetaStep
    (C.optimizerKernel K)
    (C.optimizer s)
    (C.canonicalWatkinsTarget K (C.replaceAttention s a))
attention-mediator-shared-f4-test =
  FiniteAttentionWatkinsGRUF4MediatorTheorem.sharedTargetFeedsF4
    finite-attention-watkins-gru-f4-mediator-theorem

attention-mediator-count-after-step-test :
  ∀ K s a →
  C.lcbCounts
    (C.canonicalFullStep K (C.replaceAttention s a))
  ≡
  C.lcbCounts
    (C.canonicalFullStep K s)
attention-mediator-count-after-step-test =
  FiniteAttentionWatkinsGRUF4MediatorTheorem.fullStepCountChannelInvariant
    finite-attention-watkins-gru-f4-mediator-theorem

attention-mediator-qlog-after-step-test :
  ∀ K s a →
  C.qLogValue
    (C.canonicalFullStep K (C.replaceAttention s a))
  ≡
  C.qLogValue
    (C.canonicalFullStep K s)
attention-mediator-qlog-after-step-test =
  FiniteAttentionWatkinsGRUF4MediatorTheorem.fullStepQLogChannelInvariant
    finite-attention-watkins-gru-f4-mediator-theorem

attention-mediator-norm-test :
  ∀ K s a →
  C.normPairWeightPlusOne
    (C.norm (C.canonicalFullStep K (C.replaceAttention s a)))
  ≡
  C.normPairWeightPlusOne (C.norm s)
attention-mediator-norm-test =
  FiniteAttentionWatkinsGRUF4MediatorTheorem.fullStepNormPairInvariant
    finite-attention-watkins-gru-f4-mediator-theorem

attention-mediator-persistent-gru-test :
  ∀ K s a →
  C.persistentGRU
    (C.gru (C.canonicalFullStep K (C.replaceAttention s a)))
  ≡
  C.persistentGRU (C.gru (C.replaceAttention s a))
attention-mediator-persistent-gru-test =
  FiniteAttentionWatkinsGRUF4MediatorTheorem.fullStepPersistentGRUInvariant
    finite-attention-watkins-gru-f4-mediator-theorem
