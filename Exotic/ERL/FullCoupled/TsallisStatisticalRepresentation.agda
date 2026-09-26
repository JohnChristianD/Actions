{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Carrier-polymorphic statistical representation.
--
-- This module is deliberately arithmetic-free: the abstract Law-IV
-- representation needs only Set, functions, and propositional equality.
-- A Tsallis/q-statistical interpretation may instantiate the observation
-- carrier, but no Real or Rational specialization is required here; the observation carrier is an arbitrary Set.
--
-- The representation theorem is structural. External statistical
-- literature motivates possible instantiations; it is not imported as an
-- Agda proof source.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.TsallisStatisticalRepresentation where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong)

record CarrierPolymorphicStatisticalRepresentation
  (State Observation : Set) : Set₁ where
  constructor carrierPolymorphicStatisticalRepresentation
  field
    encode : State → Observation
    decode : Observation → State
    decodeEncode : ∀ s → decode (encode s) ≡ s

open CarrierPolymorphicStatisticalRepresentation public

statisticalEncodeInjective :
  ∀ {State Observation : Set}
  (R : CarrierPolymorphicStatisticalRepresentation State Observation)
  {s t : State} →
  encode R s ≡ encode R t →
  s ≡ t
statisticalEncodeInjective R eq = cong (decode R) eq

statisticalEncodeDistinguishes :
  ∀ {State Observation : Set}
  (R : CarrierPolymorphicStatisticalRepresentation State Observation)
  {s t : State} →
  s ≢ t →
  encode R s ≢ encode R t
statisticalEncodeDistinguishes R distinct collision =
  distinct (statisticalEncodeInjective R collision)

record TsallisCompatibleStatisticalRepresentation
  (State Observation : Set) : Set₁ where
  constructor tsallisCompatibleStatisticalRepresentation
  field
    representation :
      CarrierPolymorphicStatisticalRepresentation State Observation

open TsallisCompatibleStatisticalRepresentation public

tsallisCompatibleEncodeInjective :
  ∀ {State Observation : Set}
  (R : TsallisCompatibleStatisticalRepresentation State Observation)
  {s t : State} →
  encode (representation R) s ≡ encode (representation R) t →
  s ≡ t
tsallisCompatibleEncodeInjective R =
  statisticalEncodeInjective (representation R)

tsallisCompatibleEncodeDistinguishes :
  ∀ {State Observation : Set}
  (R : TsallisCompatibleStatisticalRepresentation State Observation)
  {s t : State} →
  s ≢ t →
  encode (representation R) s ≢ encode (representation R) t
tsallisCompatibleEncodeDistinguishes R =
  statisticalEncodeDistinguishes (representation R)
