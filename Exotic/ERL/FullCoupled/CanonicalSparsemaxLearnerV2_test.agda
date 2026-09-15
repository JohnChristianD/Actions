{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalSparsemaxLearnerV2_test where

open import Relation.Binary.PropositionalEquality using (_≡_)
import Agda.Builtin.Int as I
open import Exotic.ERL.FullCoupled.CanonicalSparsemaxLearnerV2

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

check-haar : dot2 haarRow0 haarRow0 ≡ I.pos 2
check-haar = haar00

check-mobius :
  ∀ (f g h : MobiusAction) (x : Int8) →
    MobiusAction.run (composeAction (composeAction f g) h) x
      ≡ MobiusAction.run (composeAction f (composeAction g h)) x
check-mobius = mobiusAssociativity

check-persistent-gru :
  ∀ (s : GRUState) (x : Int8) →
    persistentGRU (gruStep s x) ≡ persistentGRU s
check-persistent-gru = persistentGRUMonolith
