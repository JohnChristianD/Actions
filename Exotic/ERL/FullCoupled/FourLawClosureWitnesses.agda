{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Minimal typed contract for the missing four-law closure witnesses.
--
-- This module is intentionally a contract, not an existence theorem.
-- It records exactly the semantic data that must be inhabited before
-- Law I + Law III + physics-to-learner transport can be promoted into
-- the existing Law II/Law IV composition.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.FourLawClosureWitnesses where

open import Relation.Binary.PropositionalEquality using (_≡_)

record LawIPhysicsWitness
  (LearnerState PhysicalState Current : Set) : Set₁ where
  constructor lawIPhysicsWitness
  field
    encode : LearnerState → PhysicalState
    decode : PhysicalState → LearnerState
    decodeEncode :
      ∀ s → decode (encode s) ≡ s
    trajectory :
      PhysicalState → PhysicalState
    current :
      PhysicalState → Current
    trajectoryCurrentCompatibility :
      ∀ p → current (trajectory p) ≡ current p

record LawIIIVariationalWitness
  (LearnerState PhysicalState Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary : PhysicalState → Set) : Set₁ where
  constructor lawIIIVariationalWitness
  field
    encode : LearnerState → PhysicalState
    decode : PhysicalState → LearnerState
    decodeEncode :
      ∀ s → decode (encode s) ≡ s
    variation : PhysicalState → Variation
    action : PhysicalState → Action
    admissibleVariation :
      ∀ p → Admissible (variation p)
    stationary :
      ∀ p → Stationary p

record PhysicsToLearnerTransitionWitness
  (LearnerState PhysicalState : Set)
  (learnerStep : LearnerState → LearnerState)
  (physicalStep : PhysicalState → PhysicalState) : Set₁ where
  constructor physicsToLearnerTransitionWitness
  field
    encode : LearnerState → PhysicalState
    decode : PhysicalState → LearnerState
    decodeEncode :
      ∀ s → decode (encode s) ≡ s
    stepConjugacy :
      ∀ s →
      encode (learnerStep s)
      ≡
      physicalStep (encode s)

record FourLawOneStepWitnessContract
  (LearnerState PhysicalState Current Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary : PhysicalState → Set)
  (learnerStep : LearnerState → LearnerState)
  (physicalStep : PhysicalState → PhysicalState) : Set₁ where
  constructor fourLawOneStepWitnessContract
  field
    lawI :
      LawIPhysicsWitness
        LearnerState
        PhysicalState
        Current
    lawIII :
      LawIIIVariationalWitness
        LearnerState
        PhysicalState
        Variation
        Action
        Admissible
        Stationary
    physicsToLearner :
      PhysicsToLearnerTransitionWitness
        LearnerState
        PhysicalState
        learnerStep
        physicalStep

------------------------------------------------------------------------
-- No inhabitant is supplied here. The admissibility and stationarity
-- predicates are explicit semantic obligations; this contract does not
-- manufacture them from learner algebra.
------------------------------------------------------------------------
