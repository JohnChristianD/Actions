{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalCNNBehavioralEquivalence where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using ()
open import Data.Fin using ()
open import Data.Fin.Properties using ()
open import Data.Nat.DivMod using ()
open import Data.Product using ()
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CNNLogPyramidPreservation

cnnFullStep : FullLearnerKernel → FullLearnerState → CNNLogPyramidCode → FullLearnerState
cnnFullStep K s p =
  canonicalFullStep K
    (replaceAttention s (cnnToAttention p))

cnnBehaviorallyEquivalent : CNNLogPyramidCode → CNNLogPyramidCode → Set
cnnBehaviorallyEquivalent = CNNLogPyramidEquivalent

cnnFullStep-preserves-equivalence : ∀ (K : FullLearnerKernel)
  (s : FullLearnerState) (p q : CNNLogPyramidCode) →
  cnnBehaviorallyEquivalent p q →
  cnnFullStep K s p ≡ cnnFullStep K s q
cnnFullStep-preserves-equivalence K s p q h =
  cong (canonicalFullStep K)
    (cong (replaceAttention s) h)

cnnFullStep-commutes : ∀ (K : FullLearnerKernel)
  (s : FullLearnerState) (p : CNNLogPyramidCode) →
  cnnToAttention p ≡ attention s →
  cnnFullStep K s p ≡ canonicalFullStep K s
cnnFullStep-commutes K s p h =
  cong (canonicalFullStep K) (sym (cong (replaceAttention s) h))

iterateCNN : FullLearnerKernel → CNNLogPyramidCode → Nat → FullLearnerState → FullLearnerState
iterateCNN K p zero s = s
iterateCNN K p (suc n) s =
  cnnFullStep K (iterateCNN K p n s) p

cnnTrajectory-preserves-equivalence : ∀ (K : FullLearnerKernel)
  (p q : CNNLogPyramidCode) → cnnBehaviorallyEquivalent p q →
  ∀ n s → iterateCNN K p n s ≡ iterateCNN K q n s
cnnTrajectory-preserves-equivalence K p q h zero s = refl
cnnTrajectory-preserves-equivalence K p q h (suc n) s =
  trans
    (cnnFullStep-preserves-equivalence K (iterateCNN K p n s)
      p q h)
    (cong
      (cnnFullStep K (iterateCNN K q n s) p)
      (cnnTrajectory-preserves-equivalence K p q h n s))

cnnBehavioralInterchangeability : ∀ (K : FullLearnerKernel)
  (p q : CNNLogPyramidCode) → cnnBehaviorallyEquivalent p q →
  ∀ n s →
  iterateCNN K p n s ≡ iterateCNN K q n s
cnnBehavioralInterchangeability = cnnTrajectory-preserves-equivalence

cnnDecoderIsMinimalInterface : ∀ (K : FullLearnerKernel)
  (s : FullLearnerState) (p q : CNNLogPyramidCode) →
  cnnToAttention p ≡ cnnToAttention q →
  canonicalPolicy K (replaceAttention s (cnnToAttention p)) ≡
  canonicalPolicy K (replaceAttention s (cnnToAttention q))
cnnDecoderIsMinimalInterface K s p q h =
  trans
    (canonicalPolicy-attention-invariant K s (cnnToAttention p))
    (trans
      (refl)
      (sym (canonicalPolicy-attention-invariant K s (cnnToAttention q))))

cnnEncoderSwapNoBehaviorChange : ∀ (K : FullLearnerKernel)
  (s : FullLearnerState) (p q : CNNLogPyramidCode) →
  cnnToAttention p ≡ cnnToAttention q →
  cnnFullStep K s p ≡ cnnFullStep K s q
cnnEncoderSwapNoBehaviorChange = cnnFullStep-preserves-equivalence