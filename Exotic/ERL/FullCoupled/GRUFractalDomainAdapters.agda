{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Domain adapters for the GRU-injective fractal composition seam.
--
-- These are proof-relevant contracts, not fabricated inhabitants.
-- Physics remains blocked by the concrete Law-I/Law-III witnesses.
-- Economics additionally requires a genuine inter-level transport on
-- the economic carrier, not merely a level index.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.GRUFractalDomainAdapters where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Exotic.ERL.FullCoupled.FourLawClosureWitnesses
  using
  ( FourLawOneStepWitnessContract
  )
open import Exotic.ERL.FullCoupled.GRUFractalInjectiveComposition
  using
  ( FractalInjectiveComposition
  )

record PhysicsGRUFractalAdapter
  (Level LearnerState PhysicalState Observation Current Variation Action : Set)
  (Refines : Level → Level → Set)
  (Admissible : Variation → Set)
  (Stationary : PhysicalState → Set)
  (learnerStep : LearnerState → LearnerState)
  (physicalStep : PhysicalState → PhysicalState) : Set₁ where
  constructor physicsGRUFractalAdapter
  field
    fourLawWitness :
      FourLawOneStepWitnessContract
        LearnerState
        PhysicalState
        Current
        Variation
        Action
        Admissible
        Stationary
        learnerStep
        physicalStep

    injectiveFractalRepresentation :
      FractalInjectiveComposition
        Level
        LearnerState
        Observation
        Refines

record EconomicsGRUFractalAdapter
  (Level LearnerState EconomicState Observation : Set)
  (Refines : Level → Level → Set)
  (learnerStep : LearnerState → LearnerState)
  (economicStep : EconomicState → EconomicState) : Set₁ where
  constructor economicsGRUFractalAdapter
  field
    learnerToEconomic :
      LearnerState → EconomicState
    economicToLearner :
      EconomicState → LearnerState

    learnerToEconomicInverse :
      ∀ s →
      economicToLearner (learnerToEconomic s) ≡ s

    economicToLearnerInverse :
      ∀ e →
      learnerToEconomic (economicToLearner e) ≡ e

    stepConjugacy :
      ∀ s →
      learnerToEconomic (learnerStep s) ≡
      economicStep (learnerToEconomic s)

    injectiveFractalRepresentation :
      FractalInjectiveComposition
        Level
        LearnerState
        Observation
        Refines

    economicObservation :
      EconomicState → Observation

    economicLevelTransport :
      ∀ {lower upper} →
      Refines lower upper →
      EconomicState →
      EconomicState

    economicLevelTransportInjective :
      ∀ {lower upper}
      {r : Refines lower upper}
      {x y : EconomicState} →
      economicLevelTransport r x ≡
      economicLevelTransport r y →
      x ≡ y

    economicLevelTransportRepresentation :
      ∀ {lower upper}
      (r : Refines lower upper)
      (e : EconomicState) →
      economicObservation
        (economicLevelTransport r e)
      ≡
      FractalInjectiveComposition.transport
        injectiveFractalRepresentation
        r
        (economicObservation e)

open PhysicsGRUFractalAdapter public
open EconomicsGRUFractalAdapter public
