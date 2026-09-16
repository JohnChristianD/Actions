{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearnerMonolith_test where

open import Agda.Builtin.Equality using (_≡_)
import Agda.Builtin.Int as I
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith

check-temperature : sparsemaxTemperature ≡ int8OfNat 16
check-temperature = temperatureCodeLaw

check-tie :
  fixedTemperatureSparsemax (actionScore (int8OfNat 0) (int8OfNat 0)) ≡
  int8OfNat 64 , int8OfNat 64
check-tie = temperatureTieLaw

check-positive-unit :
  fixedTemperatureSparsemax (actionScore (int8OfNat 1) (int8OfNat 0)) ≡
  int8OfNat 68 , int8OfNat 60
check-positive-unit = temperaturePositiveUnitLaw

check-negative-unit :
  fixedTemperatureSparsemax (actionScore (int8OfNat 0) (int8OfNat 1)) ≡
  int8OfNat 60 , int8OfNat 68
check-negative-unit = temperatureNegativeUnitLaw

check-qlog : ∀ x →
  negativeFiniteQLog8 x ≡
  finiteRational (negInt (numerator (finiteQLog8 x))) (denominator (finiteQLog8 x))
check-qlog = negativeFiniteQLogLaw

check-mobius : ∀ x → signedCode x ≢ I.pos 1 →
  mobiusRatio8 x ≡ finiteRational (signedCode x) (I._-_ (I.pos 1) (signedCode x))
check-mobius = mobiusRatio8-law

check-persistence :
  ∀ (s : GRUState) (x : Int8) →
  persistentGRU (gruStep s x) ≡ persistentGRU s
check-persistence = persistent-preservation

check-policy-separation :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) (a : LearnedSparsemaxAttention) →
  canonicalPolicy K (replaceAttention s a) ≡ canonicalPolicy K s
check-policy-separation = canonicalPolicy-attention-invariant

check-canonical-persistence :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) →
  persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
check-canonical-persistence = canonicalPersistentGRUPreservation

check-clock :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) →
  clock (canonicalFullStep K s) ≡ suc (clock s)
check-clock = canonicalFullStep-clock

check-count :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) →
  totalCount (canonicalFullStep K s) ≡ suc (totalCount s)
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
