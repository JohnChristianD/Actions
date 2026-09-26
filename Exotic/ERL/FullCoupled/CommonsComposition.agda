{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Nested / self-similar commons composition boundary.
--
-- The construction is deliberately proposition-valued: no Bool is needed.
-- Each level repeats the same local-optimality -> aggregate-preservation
-- obligation. A global derivation must therefore solve the obligation at
-- every inhabited level. The existing two-agent countermodel refutes that
-- unconditional implication already at one level, and hence also refutes
-- the nested version.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.CommonsComposition where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)

open import Exotic.ERL.FullCoupled.TheoremsMonolith public
  using
  ( CommonsNonDerivabilityCounterexample
  ; twoAgentCommonsCounterexample
  ; twoNotLeOne
  ; commonsWorld
  ; sharedResource
  ; resourceCapacity
  ; action
  ; extraction
  ; aggregateExtraction
  ; localOptimal
  ; allLocallyOptimal
  ; aggregateExtractionIsTwo
  ; extractionIsOne
  ; capacityIsOne
  )

------------------------------------------------------------------------
-- A single commons law repeated across an arbitrary collection of levels.
-- "Nested" here is a precise recursive/self-similar interface claim:
-- the same preservation obligation is required independently at every
-- level.
------------------------------------------------------------------------

record NestedCommonsPreservationDerivation
  (Level : Set)
  (C : CommonsNonDerivabilityCounterexample) : Set₁ where
  constructor nestedCommonsPreservationDerivation
  field
    derive :
      ∀ level →
      ∀ w →
      (∀ a →
        localOptimal C
          w
          a
          (action C w a)) →
      aggregateExtraction C w ≤
      resourceCapacity C (sharedResource C w)

open NestedCommonsPreservationDerivation public

------------------------------------------------------------------------
-- Aggregate consistency for the concrete two-agent model.
-- This makes "two-unit aggregate extraction" mathematically tied to the
-- two individual one-unit extractions rather than merely co-present fields.
------------------------------------------------------------------------

twoAgentAggregateExtractionIsSum :
  aggregateExtraction twoAgentCommonsCounterexample
    (commonsWorld twoAgentCommonsCounterexample)
  ≡
  extraction twoAgentCommonsCounterexample
    (action twoAgentCommonsCounterexample
      (inj₁ tt))
  +
  extraction twoAgentCommonsCounterexample
    (action twoAgentCommonsCounterexample
      (inj₂ tt))
twoAgentAggregateExtractionIsSum =
  trans
    (aggregateExtractionIsTwo twoAgentCommonsCounterexample)
    refl

------------------------------------------------------------------------
-- One bad level destroys an unconditional all-level derivation.
------------------------------------------------------------------------

noUnconditionalNestedCommonsPreservation :
  ∀ {Level : Set} →
  Level →
  (C : CommonsNonDerivabilityCounterexample) →
  ¬ NestedCommonsPreservationDerivation Level C
noUnconditionalNestedCommonsPreservation level C D =
  twoNotLeOne
    (subst
      (λ n → n ≤ suc zero)
      (capacityIsOne C)
      (subst
        (λ n → suc (suc zero) ≤ n)
        (aggregateExtractionIsTwo C)
        (derive D
          level
          (commonsWorld C)
          (allLocallyOptimal C))))

------------------------------------------------------------------------
-- Concrete two-scale instance: two nested levels are enough to witness
-- the impossibility. The same local/global law is demanded at each level.
------------------------------------------------------------------------

TwoScaleCommonsLevel : Set
TwoScaleCommonsLevel = ⊤ ⊎ ⊤

noUnconditionalNestedCommonsPreservation-twoScale :
  ¬ NestedCommonsPreservationDerivation
      TwoScaleCommonsLevel
      twoAgentCommonsCounterexample
noUnconditionalNestedCommonsPreservation-twoScale =
  noUnconditionalNestedCommonsPreservation
    (inj₁ tt)
    twoAgentCommonsCounterexample

------------------------------------------------------------------------
-- Scale composition rule.
--
-- A nested preservation proof is strictly stronger than a one-level proof:
-- restricting it to any inhabited level yields the corresponding local
-- preservation derivation. Thus adding more levels cannot manufacture the
-- missing local-to-global conservation invariant.
------------------------------------------------------------------------

nestedLevelRestriction :
  ∀ {Level : Set}
  {C : CommonsNonDerivabilityCounterexample} →
  (D : NestedCommonsPreservationDerivation Level C) →
  ∀ level →
  ∀ w →
  (∀ a →
    localOptimal C w a (action C w a)) →
  aggregateExtraction C w ≤
  resourceCapacity C (sharedResource C w)
nestedLevelRestriction D level =
  derive D level

------------------------------------------------------------------------
-- The unconditional graph is therefore closed at the negative boundary:
--
-- local optimality
--   -> individual extraction
--   -> aggregate extraction
--   -X-> preservation
--
-- and recursively:
--
-- level 0 -> level 1 -> ... -> level n
--   with preservation required at every inhabited level.
--
-- No Boolean encoding is involved. The propositions themselves live in Set;
-- Nat supplies the resource quantities; equality and subst transport the
-- concrete countermodel into the preservation obligation.
------------------------------------------------------------------------
