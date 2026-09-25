{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GRUStatisticalInjectivity where
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Data.Product using (_×_; _,_; proj₁)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TsallisStatisticalRepresentation public
CanonicalGRUStatisticalObservation : Set
CanonicalGRUStatisticalObservation = C.GRUState × (C.CanonicalToken → C.Int8)
canonicalGRUStatisticalEncode : C.GRUState → CanonicalGRUStatisticalObservation
canonicalGRUStatisticalEncode s = s , (λ _ → C.hiddenState s)
canonicalGRUStatisticalDecode : CanonicalGRUStatisticalObservation → C.GRUState
canonicalGRUStatisticalDecode observation = proj₁ observation
canonicalGRUStatisticalDecodeEncode : ∀ s → canonicalGRUStatisticalDecode (canonicalGRUStatisticalEncode s) ≡ s
canonicalGRUStatisticalDecodeEncode s = refl
canonicalGRUStatisticalEncodeInjective : ∀ {s t : C.GRUState} → canonicalGRUStatisticalEncode s ≡ canonicalGRUStatisticalEncode t → s ≡ t
canonicalGRUStatisticalEncodeInjective eq = cong canonicalGRUStatisticalDecode eq
record CanonicalGRUStatisticalInjectivityTheorem : Set₁ where
  constructor canonicalGRUStatisticalInjectivityTheorem
  field
    encode : C.GRUState → CanonicalGRUStatisticalObservation
    decode : CanonicalGRUStatisticalObservation → C.GRUState
    decodeEncode : ∀ s → decode (encode s) ≡ s
    injective : ∀ {s t : C.GRUState} → encode s ≡ encode t → s ≡ t
canonical-gru-statistical-injectivity-theorem : CanonicalGRUStatisticalInjectivityTheorem
canonical-gru-statistical-injectivity-theorem = canonicalGRUStatisticalInjectivityTheorem canonicalGRUStatisticalEncode canonicalGRUStatisticalDecode canonicalGRUStatisticalDecodeEncode canonicalGRUStatisticalEncodeInjective
canonicalGRUStatisticalDistinguishability : ∀ {s t : C.GRUState} → s ≢ t → canonicalGRUStatisticalEncode s ≢ canonicalGRUStatisticalEncode t
canonicalGRUStatisticalDistinguishability distinct collision = distinct (canonicalGRUStatisticalEncodeInjective collision)
canonicalGRUStatisticalStepConsequence : ∀ (s : C.GRUState) (x : C.Int8) → canonicalGRUStatisticalEncode (C.gruStep s x) ≡ (C.gruStep s x , (λ _ → C.hiddenState (C.gruStep s x)))
canonicalGRUStatisticalStepConsequence s x = refl

------------------------------------------------------------------------
-- Carrier-polymorphic Law-IV instance. The concrete canonical observation
-- remains available above, while the injectivity mechanism is now supplied
-- by the arithmetic-free representation kernel.
------------------------------------------------------------------------

canonicalGRUTsallisCompatibleRepresentation :
  TsallisCompatibleStatisticalRepresentation
    C.GRUState
    CanonicalGRUStatisticalObservation
canonicalGRUTsallisCompatibleRepresentation =
  tsallisCompatibleStatisticalRepresentation
    (carrierPolymorphicStatisticalRepresentation
      canonicalGRUStatisticalEncode
      canonicalGRUStatisticalDecode
      canonicalGRUStatisticalDecodeEncode)

canonicalGRUTsallisCompatibleInjective :
  ∀ {s t : C.GRUState} →
  encode
    (representation canonicalGRUTsallisCompatibleRepresentation) s
  ≡
  encode
    (representation canonicalGRUTsallisCompatibleRepresentation) t →
  s ≡ t
canonicalGRUTsallisCompatibleInjective =
  tsallisCompatibleEncodeInjective
    canonicalGRUTsallisCompatibleRepresentation

canonicalGRUTsallisCompatibleDistinguishability :
  ∀ {s t : C.GRUState} →
  s ≢ t →
  encode
    (representation canonicalGRUTsallisCompatibleRepresentation) s
  ≢
  encode
    (representation canonicalGRUTsallisCompatibleRepresentation) t
canonicalGRUTsallisCompatibleDistinguishability =
  tsallisCompatibleEncodeDistinguishes
    canonicalGRUTsallisCompatibleRepresentation
