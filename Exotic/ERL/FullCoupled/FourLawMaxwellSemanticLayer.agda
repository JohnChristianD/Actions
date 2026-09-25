{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Maxwell semantic closure layer.
--
-- This module separates the semantic structure supplied by the existing
-- Hodge-Maxwell representation from the additional variational/evolution
-- laws required by the four-law contracts.
--
-- It deliberately does NOT manufacture an inhabitant.  In particular:
--   * trajectory is genuine evolution data, not identity by default;
--   * current preservation is an explicit theorem obligation;
--   * variation is explicit and must be nontrivial under a supplied
--     distinction predicate;
--   * stationarity is tied to an explicit Euler-Lagrange predicate;
--   * the Maxwell action/Lagrangian is supplied as semantic data rather
--     than being faked from fieldJ.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.FourLawMaxwellSemanticLayer where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Exotic.ERL.FullCoupled.TheoremsMonolith as T
open import Exotic.ERL.FullCoupled.FourLawClosureWitnesses as F

record MaxwellEvolutionSemantics
  (Solution Form2 Form3 : Set) : Set₁ where
  constructor maxwellEvolutionSemantics
  field
    trajectory : Solution → Solution
    current : Solution → Form3
    currentPreservation :
      ∀ p → current (trajectory p) ≡ current p

record MaxwellVariationalSemantics
  (Solution Variation Action : Set)
  (Admissible : Variation → Set)
  (EulerLagrange : Solution → Set)
  (DistinctVariation : Solution → Variation → Set) : Set₁ where
  constructor maxwellVariationalSemantics
  field
    variation : Solution → Variation
    action : Solution → Action
    admissibleVariation :
      ∀ p → Admissible (variation p)
    stationary :
      ∀ p → EulerLagrange p
    nontrivialVariation :
      ∀ p → DistinctVariation p (variation p)

record MaxwellFourLawSemanticData
  (LearnerState PhysicalState Current Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary : PhysicalState → Set)
  (DistinctVariation : PhysicalState → Variation → Set)
  (learnerStep : LearnerState → LearnerState)
  (physicalStep : PhysicalState → PhysicalState) : Set₁ where
  constructor maxwellFourLawSemanticData
  field
    lawI :
      F.LawIPhysicsWitness
        LearnerState
        PhysicalState
        Current
    lawIII :
      F.LawIIIVariationalWitness
        LearnerState
        PhysicalState
        Variation
        Action
        Admissible
        Stationary
    nontrivialVariation :
      ∀ p →
      DistinctVariation
        p
        (F.LawIIIVariationalWitness.variation lawIII p)
    physicsToLearner :
      F.PhysicsToLearnerTransitionWitness
        LearnerState
        PhysicalState
        learnerStep
        physicalStep

------------------------------------------------------------------------
-- A concrete adapter from a supplied Hodge-Maxwell representation plus
-- supplied evolution/variational laws.  This is intentionally
-- conditional: the existing representation data do not themselves
-- contain current preservation or a variational action.
------------------------------------------------------------------------

maxwellLawIFromEvolution :
  ∀ {Solution Form2 Form3 : Set}
  (E : MaxwellEvolutionSemantics Solution Form2 Form3) →
  F.LawIPhysicsWitness
    Solution
    Solution
    Form3
maxwellLawIFromEvolution E =
  F.lawIPhysicsWitness
    (λ s → s)
    (λ s → s)
    (λ s → refl)
    (MaxwellEvolutionSemantics.trajectory E)
    (MaxwellEvolutionSemantics.current E)
    (MaxwellEvolutionSemantics.currentPreservation E)

maxwellLawIIIFromVariational :
  ∀ {Solution Variation Action : Set}
  {Admissible : Variation → Set}
  {EulerLagrange : Solution → Set}
  {DistinctVariation : Solution → Variation → Set}
  (V : MaxwellVariationalSemantics
    Solution
    Variation
    Action
    Admissible
    EulerLagrange
    DistinctVariation) →
  F.LawIIIVariationalWitness
    Solution
    Solution
    Variation
    Action
    Admissible
    EulerLagrange
maxwellLawIIIFromVariational V =
  F.lawIIIVariationalWitness
    (λ s → s)
    (λ s → s)
    (λ s → refl)
    (MaxwellVariationalSemantics.variation V)
    (MaxwellVariationalSemantics.action V)
    (MaxwellVariationalSemantics.admissibleVariation V)
    (MaxwellVariationalSemantics.stationary V)

------------------------------------------------------------------------
-- The existing Hodge-Maxwell carrier remains the physical carrier.
-- These definitions only identify the intended projections; they do not
-- assert the missing evolution/variational laws.
------------------------------------------------------------------------

hodgeMaxwellPhysicalState :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    T.ContinuousHodgeMaxwellExactRepresentationData
      GRU
      {Continuous = Continuous}) →
  Set
hodgeMaxwellPhysicalState W =
  T.ContinuousHodgeMaxwellExactRepresentationData.Solution W

hodgeMaxwellCurrent :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    T.ContinuousHodgeMaxwellExactRepresentationData
      GRU
      {Continuous = Continuous}) →
  T.ContinuousHodgeMaxwellExactRepresentationData.Solution W →
  T.ContinuousHodgeMaxwellExactRepresentationData.Form3 W
hodgeMaxwellCurrent W =
  T.ContinuousHodgeMaxwellExactRepresentationData.fieldJ W

------------------------------------------------------------------------
-- No closed four-law constructor is defined here.  Supplying the
-- Maxwell evolution theorem and the genuine variational theorem remains
-- the explicit frontier.
------------------------------------------------------------------------
