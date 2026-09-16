{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalSparsemaxLearnerV2_test where

open import Relation.Binary.PropositionalEquality using (_≡_)
import Agda.Builtin.Int as I
open import Exotic.ERL.FullCoupled.CanonicalSparsemaxLearnerV2
open import Exotic.ERL.FullCoupled.MobiusRational using (mobiusRatio8-law; mobiusSingularity)
open import Exotic.ERL.FullCoupled.FrozenOrthonormalWalshGRU using (walshOrthonormal; walshDimensionPowerOfFour)

check-temperature : sparsemaxTemperature ≡ int8OfNat 16
check-temperature = temperatureCodeLaw

check-tie : temperatureScaledSparsemax (actionScore (int8OfNat 0) (int8OfNat 0)) ≡ int8OfNat 64 , int8OfNat 64
check-tie = temperatureTieLaw

check-positive-unit : temperatureScaledSparsemax (actionScore (int8OfNat 1) (int8OfNat 0)) ≡ int8OfNat 68 , int8OfNat 60
check-positive-unit = temperaturePositiveUnitLaw

check-negative-unit : temperatureScaledSparsemax (actionScore (int8OfNat 0) (int8OfNat 1)) ≡ int8OfNat 60 , int8OfNat 68
check-negative-unit = temperatureNegativeUnitLaw

check-qlog : ∀ x → negativeFiniteQLog8 x ≡ finiteRational (negInt (numerator (finiteQLog8 x))) (denominator (finiteQLog8 x))
check-qlog = negativeFiniteQLogLaw

check-mobius-rational : ∀ x → signedCode x ≢ I.pos 1 →
  mobiusRatio8 x ≡ finiteRational (signedCode x) (I._-_ (I.pos 1) (signedCode x))
check-mobius-rational = mobiusRatio8-law

check-mobius-singularity : mobiusRatio8 (int8OfNat 1) ≡ zeroR
check-mobius-singularity = mobiusSingularity

check-walsh-orthonormal : walshOrthonormal ≡ walshOrthonormal
check-walsh-orthonormal = refl

check-walsh-dimension : walshDimensionPowerOfFour
check-walsh-dimension = walshDimensionPowerOfFour

check-mobius :
  ∀ (f g h : MobiusAction) (x : Int8) →
    MobiusAction.run (composeAction (composeAction f g) h) x
      ≡ MobiusAction.run (composeAction f (composeAction g h)) x
check-mobius = mobiusAssociativity

check-persistent-gru :
  ∀ (s : GRUState) (x : Int8) →
    persistentGRU (gruStep s x) ≡ persistentGRU s
check-persistent-gru = persistentGRUMonolith

check-canonical-persistent-gru :
  ∀ {A : F4Scalar} (K : FullCoupledKernel A) (s : FullCoupledState A) →
    persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
check-canonical-persistent-gru = canonicalPersistentGRUPreservation

check-attention-invariant :
  ∀ {A : F4Scalar} (K : FullCoupledKernel A) (s : FullCoupledState A) (a : LearnedSparsemaxAttention) →
    canonicalPolicy K (replaceAttention s a) ≡ canonicalPolicy K s
check-attention-invariant = canonicalPolicy-attention-invariant
