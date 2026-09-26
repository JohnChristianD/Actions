{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Arbitrary-limit closure boundary for GRU-injective fractal composition.
-- A limit object is not assumed to preserve injectivity merely because
-- every finite/indexed approximation is injective.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.GRUFractalLimitClosure where

open import Relation.Binary.PropositionalEquality using (_≡_)

record FractalLimitClosure
  (Level State Observation LimitObservation : Set)
  (Refines : Level → Level → Set)
  (encode : Level → State → Observation)
  (limitEncode : State → LimitObservation)
  : Set₁ where
  constructor fractalLimitClosure
  field
    Approx : Observation → LimitObservation → Set
    approximationWitness :
      ∀ level state →
      Approx (encode level state) (limitEncode state)
    limitSeparation :
      ∀ {s t : State} →
      limitEncode s ≡ limitEncode t →
      s ≡ t

open FractalLimitClosure public

fractalLimitInjective :
  ∀ {Level State Observation LimitObservation : Set}
  {Refines : Level → Level → Set}
  {encode : Level → State → Observation}
  {limitEncode : State → LimitObservation}
  (F : FractalLimitClosure
    Level State Observation LimitObservation
    Refines encode limitEncode) →
  ∀ {s t : State} →
  limitEncode s ≡ limitEncode t →
  s ≡ t
fractalLimitInjective F = limitSeparation F
