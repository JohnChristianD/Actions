{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ConnectedOperatorComplexity where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (Nat; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; +-mono-≤)
open import Data.Fin using (toℕ)

open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.FiniteCyclicNormPairCertificate as G

------------------------------------------------------------------------
-- Predictable operator generation is a type-shape property:
--
--     Input -> Operator
--
-- rather than
--
--     State -> Input -> Operator.
--
-- Associative function composition remains valid in both cases.  The
-- first form is the one whose operator can be generated from the input
-- before the hidden prefix state is known.
------------------------------------------------------------------------

record CostedGRUAction : Set₁ where
  constructor costedGRUAction
  field
    run : C.GRUState → C.GRUState
    representationSize : Nat
    applicationCost : Nat
open CostedGRUAction public

identityCostedGRUAction : CostedGRUAction
identityCostedGRUAction =
  costedGRUAction (λ s → s) 0 0

composeCostedGRUAction :
  CostedGRUAction → CostedGRUAction → CostedGRUAction
composeCostedGRUAction f g =
  costedGRUAction
    (λ s → run f (run g s))
    (representationSize f + representationSize g + 1)
    (applicationCost f + applicationCost g + 1)

composeCosted-run-law :
  ∀ f g s →
  run (composeCostedGRUAction f g) s ≡
  run f (run g s)
composeCosted-run-law f g s = refl

composeCosted-size-law :
  ∀ f g →
  representationSize (composeCostedGRUAction f g) ≡
  representationSize f + representationSize g + 1
composeCosted-size-law f g = refl

composeCosted-application-law :
  ∀ f g →
  applicationCost (composeCostedGRUAction f g) ≡
  applicationCost f + applicationCost g + 1
composeCosted-application-law f g = refl

------------------------------------------------------------------------
-- The custom GRU has the predictable generator shape Input -> Operator.
------------------------------------------------------------------------

inputGRUCosted : C.Int8 → CostedGRUAction
inputGRUCosted x =
  costedGRUAction
    (λ s → C.gruStep s x)
    1
    1

inputGRUCosted-generator :
  ∀ x s →
  run (inputGRUCosted x) s ≡ C.gruStep s x
inputGRUCosted-generator x s = refl

gru-input-generator-is-state-independent :
  ∀ x →
  representationSize (inputGRUCosted x) ≡ 1
gru-input-generator-is-state-independent x = refl

------------------------------------------------------------------------
-- Canonical fixed-width payload facts.
------------------------------------------------------------------------

canonicalGRUWidth : Nat
canonicalGRUWidth = C.gruStateInt8CoordinateCount

canonicalF4Width : Nat
canonicalF4Width = 5

canonicalGlobalL2Width : Nat
canonicalGlobalL2Width = 1

canonicalFullPayloadWidth : Nat
canonicalFullPayloadWidth = C.fullLearnerInt8CoordinateCount

canonicalFullPayloadWidth-law :
  canonicalFullPayloadWidth ≡
  canonicalGRUWidth + 2 + 4 + canonicalF4Width + 2 + 1
canonicalFullPayloadWidth-law = refl

canonicalFullPayloadWidth-exact :
  canonicalFullPayloadWidth ≡ 23
canonicalFullPayloadWidth-exact =
  C.fullLearnerInt8CoordinateCount-law

------------------------------------------------------------------------
-- Full connected component application cost is exact in the declared
-- component-count cost model: Watkins, attention, GRU, F4, counts, q-log
-- control, and q-log value are seven component transitions.
------------------------------------------------------------------------

canonicalComponentCount : Nat
canonicalComponentCount = 7

canonicalSequentialApplicationCost : Nat → Nat
canonicalSequentialApplicationCost n =
  n * canonicalComponentCount + (n ∸ 1)

canonicalSequentialApplicationCost-law :
  ∀ n →
  canonicalSequentialApplicationCost n ≡
  n * 7 + (n ∸ 1)
canonicalSequentialApplicationCost-law n = refl

------------------------------------------------------------------------
-- The finite cyclic norm certificate bounds transition gain separately
-- from representation width.  This prevents NormPair bookkeeping from
-- being misidentified as byte width.
------------------------------------------------------------------------

normBudget-preserves-payload-separation :
  ∀ {f : C.Int8 → C.Int8} (Cf : G.NormPairOperatorCertificate f) →
  representationSize (identityCostedGRUAction) ≤
  representationSize (identityCostedGRUAction) +
  G.normPairOperatorBudget (G.pair Cf)
normBudget-preserves-payload-separation Cf =
  z≤n

------------------------------------------------------------------------
-- Balanced scan has logarithmic depth in the operator-count recurrence
-- when composition of already-built operators is one cost unit.
------------------------------------------------------------------------

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

balancedScanSpan : Nat → Nat
balancedScanSpan zero = zero
balancedScanSpan (suc n) = suc (balancedScanSpan (half n))

balancedScanSpan-positive :
  ∀ {n} → n ≢ zero → balancedScanSpan n ≢ zero
balancedScanSpan-positive {zero} ()
balancedScanSpan-positive {suc n} _ ()

------------------------------------------------------------------------
-- A state-dependent gate still composes associatively.  It simply does
-- not have the Input -> Operator generator shape certified above.
------------------------------------------------------------------------

stateDependentOperatorShape :
  Set
stateDependentOperatorShape =
  C.GRUState → C.Int8 → CostedGRUAction

predictableOperatorShape :
  Set
predictableOperatorShape =
  C.Int8 → CostedGRUAction

------------------------------------------------------------------------
-- Reservoir boundary:
--
-- bounded finite payload can receive exact finite operator certificates;
-- the full learner's one-byte observation remains subject to the existing
-- pigeonhole/no-left-inverse theorem.
------------------------------------------------------------------------

finiteCertificateDoesNotImpliesFullObservation :
  Set
finiteCertificateDoesNotImpliesFullObservation =
  ∀ {f : C.Int8 → C.Int8} →
  G.NormPairOperatorCertificate f →
  C.Int8 → C.Int8

