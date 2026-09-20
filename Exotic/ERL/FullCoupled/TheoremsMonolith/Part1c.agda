{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TheoremsMonolith.Part1c where

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

open import Exotic.ERL.FullCoupled.TheoremsMonolith.Part1b public

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



