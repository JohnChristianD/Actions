{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CNNLogPyramidComplete where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Fin using (Fin)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CNNLogPyramidPreservation

-- The minimal active composition is exactly the decoder-to-GRU path used by
-- the maintained learner. The raw Fin-64 code is deliberately not claimed
-- to affect the transition unless it changes the decoder summary.
record CNNMinimalComposition : Set₁ where
  constructor cnnMinimalComposition
  field
    decode : CNNLogPyramidCode → LearnedSparsemaxAttention
    sparsemax : LearnedSparsemaxAttention → Sparsemax2Pair
    lift : Sparsemax2Pair → IntVec4
    walsh : IntVec4 → WalshVec4
    toGRU : WalshVec4 → Int8
    step : GRUState → Int8 → GRUState

open CNNMinimalComposition public

canonicalCNNMinimalComposition : FullLearnerKernel → CNNMinimalComposition
canonicalCNNMinimalComposition K = cnnMinimalComposition
  cnnToAttention
  learnedSparsemaxAttentionWeights
  liftAttention
  walshHadamardApply
  (attentionToGRU K)
  gruStep

cnnMinimalGRUInput : FullLearnerKernel → FullLearnerState → CNNLogPyramidCode → Int8
cnnMinimalGRUInput K s p =
  int8Add (canonicalSignal K s)
    (attentionToGRU K
      (walshHadamardApply
        (liftAttention
          (learnedSparsemaxAttentionWeights (cnnToAttention p)))))

cnnMinimalGRUStep : FullLearnerKernel → FullLearnerState → CNNLogPyramidCode → GRUState
cnnMinimalGRUStep K s p =
  gruStep (gru s) (cnnMinimalGRUInput K s p)

cnnLogPyramid-factorization : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p : CNNLogPyramidCode) →
  cnnMinimalGRUStep K s p ≡ cnnLogPyramidGRUStep K s p
cnnLogPyramid-factorization K s p = refl

cnnLogPyramid-quotient : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p q : CNNLogPyramidCode) →
  cnnToAttention p ≡ cnnToAttention q →
  cnnMinimalGRUInput K s p ≡ cnnMinimalGRUInput K s q
cnnLogPyramid-quotient K s p q h =
  cnnLogPyramidEncoding-preserves-input K s p q h

cnnLogPyramid-transition-congruence : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p q : CNNLogPyramidCode) →
  cnnToAttention p ≡ cnnToAttention q →
  cnnMinimalGRUStep K s p ≡ cnnMinimalGRUStep K s q
cnnLogPyramid-transition-congruence K s p q h =
  cnnLogPyramidGRUInputPreservation K s p q h

-- A finite four-level hierarchy makes the word "pyramid" structural rather
-- than metaphorical. Refinement is an explicit relation; no logarithmic
-- depth or compression claim is hidden in the type.
data PyramidLevel : Set where
  level0 level1 level2 level3 : PyramidLevel

record CNNLogPyramidHierarchy : Set₁ where
  constructor cnnLogPyramidHierarchy
  field
    levelCode : PyramidLevel → CNNLogPyramidCode
    parent : PyramidLevel → PyramidLevel
    refineWitness : ∀ {l} → l ≢ level0 → parent l ≢ l
open CNNLogPyramidHierarchy public

cnnLogPyramidHierarchy-congruence : ∀ (H : CNNLogPyramidHierarchy)
  (K : FullLearnerKernel) (s : FullLearnerState)
  (l₁ l₂ : PyramidLevel) →
  cnnToAttention (levelCode H l₁) ≡ cnnToAttention (levelCode H l₂) →
  cnnMinimalGRUStep K s (levelCode H l₁) ≡
  cnnMinimalGRUStep K s (levelCode H l₂)
cnnLogPyramidHierarchy-congruence H K s l₁ l₂ h =
  cnnLogPyramid-transition-congruence K s (levelCode H l₁) (levelCode H l₂) h

cnnLogPyramid-commutes : ∀ (K : FullLearnerKernel) (s : FullLearnerState)
  (p : CNNLogPyramidCode) →
  cnnToAttention p ≡ attention s →
  cnnMinimalGRUStep K s p ≡ canonicalGRUStep K s
cnnLogPyramid-commutes K s p h =
  cnnLogPyramidCommutesWithCanonicalGRU K s p h

-- No bijection, inverse decoder, metric approximation, or function-class
-- separation is asserted: those require additional semantic structure that
-- the current finite carrier does not provide.
