{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CNNLogPyramidPreservation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using ()
open import Data.Fin using (Fin)
open import Data.Fin.Properties using ()
open import Data.Nat.DivMod using ()
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith

CNNLogPyramid64 : Set
CNNLogPyramid64 = Fin 64 → Int8

record CNNLogPyramidCode : Set where
  constructor cnnLogPyramidCode
  field
    encode64 : CNNLogPyramid64
    leftSummary rightSummary : Int8
open CNNLogPyramidCode public

cnnToAttention : CNNLogPyramidCode → LearnedSparsemaxAttention
cnnToAttention p = learnedSparsemaxAttention (leftSummary p) (rightSummary p)

CNNLogPyramidEquivalent : CNNLogPyramidCode → CNNLogPyramidCode → Set
CNNLogPyramidEquivalent p q = cnnToAttention p ≡ cnnToAttention q

cnnLogPyramidEquivalent-refl : ∀ p → CNNLogPyramidEquivalent p p
cnnLogPyramidEquivalent-refl p = refl

cnnLogPyramidEquivalent-sym : ∀ p q → CNNLogPyramidEquivalent p q → CNNLogPyramidEquivalent q p
cnnLogPyramidEquivalent-sym p q h = sym h

cnnLogPyramidEquivalent-trans : ∀ p q r →
  CNNLogPyramidEquivalent p q → CNNLogPyramidEquivalent q r →
  CNNLogPyramidEquivalent p r
cnnLogPyramidEquivalent-trans p q r h₁ h₂ = trans h₁ h₂

cnnLogPyramidGRUStep : FullLearnerKernel → FullLearnerState → CNNLogPyramidCode → GRUState
cnnLogPyramidGRUStep K s p =
  gruStep (gru s)
    (int8Add (canonicalSignal K s)
      (attentionToGRU K
        (walshHadamardApply
          (liftAttention (learnedSparsemaxAttentionWeights (cnnToAttention p))))))

cnnLogPyramidGRUInputPreservation : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p q : CNNLogPyramidCode) → CNNLogPyramidEquivalent p q →
  cnnLogPyramidGRUStep K s p ≡ cnnLogPyramidGRUStep K s q
cnnLogPyramidGRUInputPreservation K s p q h = cong
  (λ a → gruStep (gru s)
    (int8Add (canonicalSignal K s)
      (attentionToGRU K
        (walshHadamardApply
          (liftAttention (learnedSparsemaxAttentionWeights a)))))) h

cnnLogPyramidStepPreservation : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p q : CNNLogPyramidCode) → CNNLogPyramidEquivalent p q →
  cnnLogPyramidGRUStep K s p ≡ cnnLogPyramidGRUStep K s q
cnnLogPyramidStepPreservation = cnnLogPyramidGRUInputPreservation

cnnLogPyramidCommutesWithCanonicalGRU : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p : CNNLogPyramidCode) → cnnToAttention p ≡ attention s →
  cnnLogPyramidGRUStep K s p ≡ canonicalGRUStep K s
cnnLogPyramidCommutesWithCanonicalGRU K s p h =
  cong
    (λ a → gruStep (gru s)
      (int8Add (canonicalSignal K s)
        (attentionToGRU K
          (walshHadamardApply
            (liftAttention (learnedSparsemaxAttentionWeights a)))))) h

cnnLogPyramidEncoding-preserves-input : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p q : CNNLogPyramidCode) → CNNLogPyramidEquivalent p q →
  (int8Add (canonicalSignal K s)
    (attentionToGRU K
      (walshHadamardApply
        (liftAttention (learnedSparsemaxAttentionWeights (cnnToAttention p)))))) ≡
  (int8Add (canonicalSignal K s)
    (attentionToGRU K
      (walshHadamardApply
        (liftAttention (learnedSparsemaxAttentionWeights (cnnToAttention q))))))
cnnLogPyramidEncoding-preserves-input K s p q h =
  cong
    (λ a → int8Add (canonicalSignal K s)
      (attentionToGRU K
        (walshHadamardApply
          (liftAttention (learnedSparsemaxAttentionWeights a))))) h
