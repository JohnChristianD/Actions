{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.EconomicArrowDebreuGate where

------------------------------------------------------------------------
-- Emergent-only Arrow–Debreu specialization.
--
-- Arrow–Debreu is intentionally NOT a primitive equilibrium carrier.
-- A specialization value can only be constructed from the generalized
-- equilibrium plus the explicit classical conditions required by the
-- chosen specialization theorem.
--
-- This module is a gate/certificate interface. It does not claim that
-- the classical assumptions are derivable from generalized equilibrium.
-- They must be supplied by an actual construction/theorem.
------------------------------------------------------------------------

record ArrowDebreuConditions
  (Commodity Allocation : Set) : Set₁ where
  constructor arrowDebreuConditions
  field
    finiteDimensionalCommodities :
      Set

    ownBundlePreferences :
      Set

    classicalBudgetOwnership :
      Set

    convexityContinuity :
      Set

    competitiveProduction :
      Set

    classicalFeasibilityClearing :
      Set

------------------------------------------------------------------------
-- The semantic payload is deliberately abstract here.
--
-- The gate does not manufacture an equilibrium or a price.  The caller
-- must provide the already-established generalized equilibrium witness.
-- This prevents the Arrow–Debreu name from becoming an alternate
-- equilibrium primitive.
------------------------------------------------------------------------

record ArrowDebreuSpecialization
  (GeneralizedEquilibrium : Set)
  (Commodity Allocation : Set) : Set₁ where
  constructor arrowDebreuSpecialization
  field
    generalizedEquilibrium :
      GeneralizedEquilibrium

    classicalConditions :
      ArrowDebreuConditions Commodity Allocation

------------------------------------------------------------------------
-- The actual e-graph gate.
--
-- No classical specialization edge exists unless every required
-- condition is present.  In particular, generalized equilibrium alone
-- cannot reduce to Arrow–Debreu.
------------------------------------------------------------------------

record ArrowDebreuGate
  (GeneralizedEquilibrium Commodity Allocation : Set) : Set₁ where
  constructor arrowDebreuGate
  field
    specialize :
      GeneralizedEquilibrium →
      ArrowDebreuConditions Commodity Allocation →
      ArrowDebreuSpecialization
        GeneralizedEquilibrium
        Commodity
        Allocation

------------------------------------------------------------------------
-- Canonical gate implementation.
--
-- This is intentionally structural: it packages the generalized
-- equilibrium and the classical conditions without inventing any missing
-- economic theorem.  A stronger specialization theorem can later replace
-- this constructor with a proof-producing implementation.
------------------------------------------------------------------------

arrowDebreuGate :
  ∀ {GeneralizedEquilibrium Commodity Allocation : Set} →
  ArrowDebreuGate
    GeneralizedEquilibrium
    Commodity
    Allocation
arrowDebreuGate =
  arrowDebreuGate
    (λ equilibrium conditions →
      arrowDebreuSpecialization
        equilibrium
        conditions)

------------------------------------------------------------------------
-- Negative boundary:
--
-- There is deliberately no function of the form
--
--   GeneralizedEquilibrium → ArrowDebreuSpecialization
--
-- because that implication would erase the classical hypotheses.
--
-- Likewise there is no
--
--   Price → ArrowDebreuSpecialization
--   KKT → ArrowDebreuSpecialization
--   MarketClearing → ArrowDebreuSpecialization
--
-- The e-graph therefore cannot legally collapse those classes into the
-- Arrow–Debreu specialization without first producing the condition
-- certificate above.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Emergent-necessity witness.
--
-- This records the stronger claim needed before treating Arrow–Debreu as
-- a retained e-graph class: a downstream theorem explicitly consumes the
-- classical condition package.
------------------------------------------------------------------------

record ArrowDebreuNecessaryFor
  (GeneralizedEquilibrium Commodity Allocation Theorem : Set) : Set₁ where
  constructor arrowDebreuNecessaryFor
  field
    consumesClassicalConditions :
      GeneralizedEquilibrium →
      ArrowDebreuConditions Commodity Allocation →
      Theorem

------------------------------------------------------------------------
-- If no downstream theorem consumes Arrow–Debreu conditions, the label is
-- semantically eliminable.  The repository can therefore keep the
-- generalized surface without carrying a redundant classical node.
------------------------------------------------------------------------
