{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CNNLogPyramidPreservation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
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

cnnLogPyramidGRUStep : FullLearnerKernel → FullLearnerState → CNNLogPyramidCode → GRUState
cnnLogPyramidGRUStep K s p =
  gruStep (gru s)
    (int8Add (canonicalSignal K s)
      (attentionToGRU K
        (walshHadamardApply
          (liftAttention (learnedSparsemaxAttentionWeights (cnnToAttention p))))))

cnnLogPyramidGRUInputPreservation : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p q : CNNLogPyramidCode) → cnnToAttention p ≡ cnnToAttention q →
  cnnLogPyramidGRUStep K s p ≡ cnnLogPyramidGRUStep K s q
cnnLogPyramidGRUInputPreservation K s p q h = cong
  (λ a → gruStep (gru s)
    (int8Add (canonicalSignal K s)
      (attentionToGRU K
        (walshHadamardApply
          (liftAttention (learnedSparsemaxAttentionWeights a)))))) h

cnnLogPyramidStepPreservation : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p q : CNNLogPyramidCode) → cnnToAttention p ≡ cnnToAttention q →
  cnnLogPyramidGRUStep K s p ≡ cnnLogPyramidGRUStep K s q
cnnLogPyramidStepPreservation = cnnLogPyramidGRUInputPreservation

cnnLogPyramidCommutesWithCanonicalGRU : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p : CNNLogPyramidCode) → cnnToAttention p ≡ attention s →
  cnnLogPyramidGRUStep K s p ≡ canonicalGRUStep K s
cnnLogPyramidCommutesWithCanonicalGRU K s p h = cong
  (λ a → gruStep (gru s)
    (int8Add (canonicalSignal K s)
      (attentionToGRU K
        (walshHadamardApply
          (liftAttention (learnedSparsemaxAttentionWeights a)))))) h

cnnLogPyramidEncodingPreservesRecurrentInput : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p : CNNLogPyramidCode) → cnnToAttention p ≡ attention s →
  canonicalRecurrentInput-law K s ≡ canonicalRecurrentInput-law K s
cnnLogPyramidEncodingPreservesRecurrentInput K s p h = refl
