{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Decoder survival through a fractal limit.
--
-- This module isolates the exact missing seam after finite/indexed GRU
-- injectivity: a compatible family of finite decoders must determine a
-- single decoder on the limit carrier.
--
-- No topological limit or existence claim is manufactured here.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.GRUFractalLimitDecoderSurvival where

open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)

record CoherentLimitDecoder
  (Level State Observation LimitObservation : Set)
  (encode : Level → State → Observation)
  (limitEncode : State → LimitObservation)
  : Set₁ where
  constructor coherentLimitDecoder
  field
    decode : Level → Observation → State
    limitDecode : LimitObservation → State
    projection : Level → LimitObservation → Observation
    projectionEncode :
      ∀ level state →
      projection level (limitEncode state) ≡ encode level state
    decoderCoherence :
      ∀ level limitObservation →
      decode level (projection level limitObservation) ≡
      limitDecode limitObservation

open CoherentLimitDecoder public

coherentLimitDecoder-left-inverse :
  ∀ {Level State Observation LimitObservation : Set}
  {encode : Level → State → Observation}
  {limitEncode : State → LimitObservation}
  (C :
    CoherentLimitDecoder
      Level State Observation LimitObservation
      encode limitEncode) →
  ∀ level state →
  decode C level (encode level state) ≡ state →
  limitDecode C (limitEncode state) ≡ state
coherentLimitDecoder-left-inverse C level state finiteLeftInverse =
  trans
    (sym (decoderCoherence C level (limitEncode state)))
    (trans
      (cong (decode C level) (projectionEncode C level state))
      finiteLeftInverse)

------------------------------------------------------------------------
-- The graph edge represented by this module is:
--
--   finite decoder left inverse
--     + limit projection
--     + projection/encoding compatibility
--     + decoder coherence
--     -> limit-surviving left inverse
--
-- Once the resulting limit decoder is available, the existing
-- GRUFractalEGraphAStarLimitComposition module derives limit injectivity.
------------------------------------------------------------------------
