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

open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)
open import Data.List using (List; []; _∷_)

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
-- Generic autonomous-time lifting of the physics-to-learner square.
-- This is proof infrastructure only; it does not create a missing
-- physics witness.
------------------------------------------------------------------------

iterateStep :
  ∀ {State : Set} →
  (State → State) →
  Nat →
  State →
  State
iterateStep step zero s = s
iterateStep step (suc n) s = iterateStep step n (step s)

iterateConjugacy :
  ∀ {LearnerState PhysicalState : Set}
  {learnerStep : LearnerState → LearnerState}
  {physicalStep : PhysicalState → PhysicalState}
  (encode : LearnerState → PhysicalState)
  (stepConjugacy :
    ∀ s →
    encode (learnerStep s) ≡
    physicalStep (encode s)) →
  ∀ n s →
  encode (iterateStep learnerStep n s)
  ≡
  iterateStep physicalStep n (encode s)
iterateConjugacy encode stepConjugacy zero s = refl
iterateConjugacy encode stepConjugacy (suc n) s =
  trans
    (iterateConjugacy
      encode
      stepConjugacy
      n
      (learnerStep s))
    (cong
      (iterateStep physicalStep n)
      (stepConjugacy s))

------------------------------------------------------------------------
-- Input-indexed square contract for prefix scans. This is deliberately
-- separate from the autonomous iterate witness: a prefix consumes an
-- input at every step, so the commuting law must quantify over input.
------------------------------------------------------------------------

record InputIndexedConjugacy
  (LearnerState PhysicalState Input : Set) : Set₁ where
  constructor inputIndexedConjugacy
  field
    encode : LearnerState → PhysicalState
    learnerStep : LearnerState → Input → LearnerState
    physicalStep : PhysicalState → Input → PhysicalState
    stepConjugacy :
      ∀ s x →
      encode (learnerStep s x)
      ≡
      physicalStep (encode s) x

open InputIndexedConjugacy public

prefixScan :
  ∀ {State Input : Set} →
  (State → Input → State) →
  List Input →
  State →
  State
prefixScan step [] s = s
prefixScan step (x ∷ xs) s =
  prefixScan step xs (step s x)

prefixScanConjugacy :
  ∀ {LearnerState PhysicalState Input : Set}
  (R : InputIndexedConjugacy LearnerState PhysicalState Input) →
  ∀ xs s →
  encode R (prefixScan (learnerStep R) xs s)
  ≡
  prefixScan (physicalStep R) xs (encode R s)
prefixScanConjugacy R [] s = refl
prefixScanConjugacy R (x ∷ xs) s =
  trans
    (prefixScanConjugacy
      R
      xs
      (learnerStep R s x))
    (cong
      (prefixScan (physicalStep R) xs)
      (stepConjugacy R s x))

------------------------------------------------------------------------
-- No inhabitant is supplied here. The admissibility and stationarity
-- predicates are explicit semantic obligations; these contracts do not
-- manufacture them from learner algebra.
------------------------------------------------------------------------
