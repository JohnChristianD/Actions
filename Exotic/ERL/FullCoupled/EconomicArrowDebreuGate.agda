{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.EconomicArrowDebreuGate where

------------------------------------------------------------------------
-- Emergent-only Arrow–Debreu specialization.
--
-- Arrow–Debreu is not a primitive equilibrium carrier.
-- The generalized economic surface remains primary.  A classical
-- specialization exists only when its additional conditions are actually
-- supplied or derived.
------------------------------------------------------------------------

record ArrowDebreuConditions
  (Commodity Allocation : Set) : Set₁ where
  constructor arrowDebreuConditions
  field
    finiteDimensionalCommodities : Set
    ownBundlePreferences : Set
    classicalBudgetOwnership : Set
    convexityContinuity : Set
    competitiveProduction : Set
    classicalFeasibilityClearing : Set

------------------------------------------------------------------------
-- The specialization payload.
------------------------------------------------------------------------

record ArrowDebreuSpecialization
  (GeneralizedEquilibrium : Set)
  (Commodity Allocation : Set) : Set₁ where
  constructor arrowDebreuSpecialization
  field
    generalizedEquilibrium : GeneralizedEquilibrium
    classicalConditions :
      ArrowDebreuConditions Commodity Allocation

------------------------------------------------------------------------
-- The only retained Arrow–Debreu edge is a derivation of its additional
-- conditions.  There is no generic gate that merely repackages supplied
-- certificates.
------------------------------------------------------------------------

record ArrowDebreuConditionDerivation
  (GeneralizedStructure Commodity Allocation : Set) : Set₁ where
  constructor arrowDebreuConditionDerivation
  field
    derive :
      GeneralizedStructure →
      ArrowDebreuConditions Commodity Allocation

------------------------------------------------------------------------
-- Once the derivation exists, specialization is ordinary construction.
-- If no such derivation can be proved and no downstream theorem consumes
-- these conditions, the Arrow–Debreu node is eliminable from the e-graph.
------------------------------------------------------------------------

specializeFromDerivedConditions :
  ∀ {GeneralizedStructure Commodity Allocation : Set} →
  ArrowDebreuConditionDerivation
    GeneralizedStructure
    Commodity
    Allocation →
  (generalizedEquilibrium : GeneralizedStructure) →
  ArrowDebreuSpecialization
    GeneralizedStructure
    Commodity
    Allocation
specializeFromDerivedConditions
  derivation
  generalizedEquilibrium =
  arrowDebreuSpecialization
    generalizedEquilibrium
    (ArrowDebreuConditionDerivation.derive
      derivation
      generalizedEquilibrium)

------------------------------------------------------------------------
-- Emergent necessity witness.
--
-- Arrow–Debreu is retained only when a downstream theorem genuinely
-- consumes the classical condition package.
------------------------------------------------------------------------

record ArrowDebreuNecessaryFor
  (GeneralizedEquilibrium Commodity Allocation Theorem : Set) : Set₁ where
  constructor arrowDebreuNecessaryFor
  field
    consumesClassicalConditions :
      GeneralizedEquilibrium →
      ArrowDebreuConditions Commodity Allocation →
      Theorem
