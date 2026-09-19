{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearnerMonolith_test where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith

check-temperature : sparsemaxTemperature ≡ int8OfNat 16
check-temperature = temperatureCodeLaw

check-tie :
  fixedTemperatureSparsemax (actionScore (int8OfNat 0) (int8OfNat 0)) ≡
  (int8OfNat 64 , int8OfNat 64)
check-tie = temperatureTieLaw

check-positive-unit :
  fixedTemperatureSparsemax (actionScore (int8OfNat 1) (int8OfNat 0)) ≡
  (int8OfNat 68 , int8OfNat 60)
check-positive-unit = temperaturePositiveUnitLaw

check-negative-unit :
  fixedTemperatureSparsemax (actionScore (int8OfNat 0) (int8OfNat 1)) ≡
  (int8OfNat 60 , int8OfNat 68)
check-negative-unit = temperatureNegativeUnitLaw

check-qlog : ∀ x →
  negativeFiniteQLog8 x ≡
  finiteRational 1 (numerator (finiteQLog8 x)) (denominator (finiteQLog8 x))
check-qlog = negativeFiniteQLogLaw

check-persistence : ∀ (s : GRUState) (x : Int8) →
  persistentGRU (gruStep s x) ≡ persistentGRU s
check-persistence = persistent-preservation

check-gru-equivalence : ∀ (s : GRUState) → GRUEquivalent s s
check-gru-equivalence = gruEquivalent-refl

check-gru-equivalence-respect : ∀ (s t : GRUState) (x : Int8) →
  GRUEquivalent s t → GRUEquivalent (gruStep s x) (gruStep t x)
check-gru-equivalence-respect = gruStep-respects-equivalence

check-gru-scan : ∀ x y z s →
  runGRU (composeGRUAction (composeGRUAction (inputGRUAction x) (inputGRUAction y))
    (inputGRUAction z)) s ≡
  runGRU (composeGRUAction (inputGRUAction x)
    (composeGRUAction (inputGRUAction y) (inputGRUAction z))) s
check-gru-scan = gruInputActionAssociativity

check-h4-orthogonality : H4GramLaw
check-h4-orthogonality = walshHadamardOrthogonality4

check-power4-width : PowerOfFour canonicalWalshWidth
check-power4-width = canonicalWalshWidth-power4

check-pure-int8-count : gruCriticWH8CoordinateCount ≡ 15
check-pure-int8-count = gruCriticWH8CoordinateCount-law

check-quotient-count : gruCriticWH8PersistentQuotientCoordinateCount ≡ 14
check-quotient-count = gruCriticWH8PersistentQuotientCoordinateCount-law

check-full-int8-count : fullLearnerInt8CoordinateCount ≡ 23
check-full-int8-count = fullLearnerInt8CoordinateCount-law

check-policy-separation :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) (a : LearnedSparsemaxAttention) →
  canonicalPolicy K (replaceAttention s a) ≡ canonicalPolicy K s
check-policy-separation = canonicalPolicy-attention-invariant

check-canonical-persistence :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) →
  persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
check-canonical-persistence = canonicalPersistentGRUPreservation

check-hard-sparsity-composition :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState)
    (n : NormPair) (o : F4IntUState) →
  HardSparseLeft (canonicalPolicy K s) →
  HardSparseLeft (canonicalPolicy K (replaceNorm (replaceOptimizer s o) n))
check-hard-sparsity-composition = hardSparse-composition-normPair-F4-L2

check-clock :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) →
  clock (canonicalFullStep K s) ≡ suc (clock s)
check-clock = canonicalFullStep-clock

check-count :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) →
  totalCount (lcbCounts (canonicalFullStep K s)) ≡
  suc (totalCount (lcbCounts s))
check-count = canonicalTotalCountStep

check-no-fixed-point :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) →
  canonicalFullStep K s ≢ s
check-no-fixed-point = canonicalNoFixedPoint

check-aperiodic :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) (n : Nat) →
  iterateCanonical K (suc n) s ≢ s
check-aperiodic = canonicalAperiodic

check-no-cycle :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) (n : Nat) →
  iterateCanonical K (suc n) s ≡ s → ⊥
check-no-cycle = canonicalNoNontrivialFiniteCycle

check-no-counted-two-cycle :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) →
  iterateCanonical K 2 s ≡ s → ⊥
check-no-counted-two-cycle = canonicalNoCountedTwoCycle
