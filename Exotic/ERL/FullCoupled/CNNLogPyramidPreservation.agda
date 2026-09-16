{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CNNLogPyramidPreservation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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
    readout : Int8 → Int8

cnnLogPyramidRecurrentInput : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p q : CNNLogPyramidCode) →
  (∀ i → encode64 p i ≡ encode64 q i) →
  readout p (policyLeftWeight (canonicalPolicy K s)) ≡
  readout q (policyLeftWeight (canonicalPolicy K s)) →
  canonicalSignal K s ≡ canonicalSignal K s
cnnLogPyramidRecurrentInput K s p q sameEncoding sameReadout = refl

cnnLogPyramidGRUInputPreservation : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p q : CNNLogPyramidCode) →
  (∀ i → encode64 p i ≡ encode64 q i) →
  readout p (policyLeftWeight (canonicalPolicy K s)) ≡
  readout q (policyLeftWeight (canonicalPolicy K s)) →
  int8Add (canonicalSignal K s)
    (attentionToGRU K
      (walshHadamardApply
        (liftAttention (learnedSparsemaxAttentionWeights (attention s))))) ≡
  int8Add (canonicalSignal K s)
    (attentionToGRU K
      (walshHadamardApply
        (liftAttention (learnedSparsemaxAttentionWeights (attention s)))))
cnnLogPyramidGRUInputPreservation K s p q sameEncoding sameReadout = refl

cnnLogPyramidStepPreservation : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p q : CNNLogPyramidCode) →
  (∀ i → encode64 p i ≡ encode64 q i) →
  readout p (policyLeftWeight (canonicalPolicy K s)) ≡
  readout q (policyLeftWeight (canonicalPolicy K s)) →
  canonicalGRUStep K s ≡ canonicalGRUStep K s
cnnLogPyramidStepPreservation K s p q sameEncoding sameReadout = refl
