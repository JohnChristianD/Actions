{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearnerMonolith_test where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin using (Fin)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith

check-temperature : sparsemaxTemperature ≡ 16
check-temperature = temperatureCodeLaw

check-generic-policy :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalPolicy K s ≡
  sparsemaxPolicy
    (actionSpaceK K)
    (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s)))
    (valuesCount (lcbCounts s))
check-generic-policy K s = refl

check-policy-separation :
  ∀ (K : CanonicalFullLearnerKernel)
    (s : CanonicalFullLearnerState)
    (a : LearnedSparsemaxAttention canonicalActionCount) →
  canonicalPolicy K (replaceAttention s a) ≡ canonicalPolicy K s
check-policy-separation = canonicalPolicy-attention-invariant

check-canonical-persistence :
  ∀ (K : CanonicalFullLearnerKernel) (s : CanonicalFullLearnerState) →
  persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
check-canonical-persistence = canonicalPersistentGRUPreservation

check-hard-sparsity-composition :
  ∀ (K : CanonicalFullLearnerKernel) (s : CanonicalFullLearnerState)
    (n : NormPair) (o : F4IntUState) →
  HardSparse K s →
  HardSparse K (replaceNorm (replaceOptimizer s o) n)
check-hard-sparsity-composition = hardSparse-composition-normPair-F4-L2

check-clock :
  ∀ (K : CanonicalFullLearnerKernel) (s : CanonicalFullLearnerState) →
  clock (canonicalFullStep K s) ≡ suc (clock s)
check-clock = canonicalFullStep-clock

check-count :
  ∀ (K : CanonicalFullLearnerKernel) (s : CanonicalFullLearnerState) →
  totalCount (lcbCounts (canonicalFullStep K s)) ≡
  suc (totalCount (lcbCounts s))
check-count = canonicalTotalCountStep

check-no-fixed-point :
  ∀ (K : CanonicalFullLearnerKernel) (s : CanonicalFullLearnerState) →
  canonicalFullStep K s ≢ s
check-no-fixed-point = canonicalNoFixedPoint

check-aperiodic :
  ∀ (K : CanonicalFullLearnerKernel) (s : CanonicalFullLearnerState) (n : Nat) →
  iterateCanonical K (suc n) s ≢ s
check-aperiodic = canonicalAperiodic

check-no-cycle :
  ∀ (K : CanonicalFullLearnerKernel) (s : CanonicalFullLearnerState) (n : Nat) →
  iterateCanonical K (suc n) s ≡ s → ⊥
check-no-cycle = canonicalNoNontrivialFiniteCycle

check-no-counted-two-cycle :
  ∀ (K : CanonicalFullLearnerKernel) (s : CanonicalFullLearnerState) →
  iterateCanonical K 2 s ≡ s → ⊥
check-no-counted-two-cycle = canonicalNoCountedTwoCycle

check-hard-sign-idempotent :
  ∀ x → hardSignGate (hardSignGate x) ≡ hardSignGate x
check-hard-sign-idempotent x with hardSign x
... | negative = refl
... | zeroSign = refl
... | positive = refl
