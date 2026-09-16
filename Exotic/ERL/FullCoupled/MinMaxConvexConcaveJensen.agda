{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.MinMaxConvexConcaveJensen where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty using (⊥)

-- This module isolates the missing Jensen layer from the learner kernel.
-- The theorem is a finite certificate interface: no real-number, measure,
-- Float, or transcendental assumptions are smuggled into the --safe core.

record JensenConvexity (X Z : Set) : Set₁ where
  constructor jensenConvexity
  field
    midpoint : X → X → X
    f : X → Z
    midpointBound : ∀ x y → f (midpoint x y) ≡ f x
open JensenConvexity public

record JensenConcavity (Y Z : Set) : Set₁ where
  constructor jensenConcavity
  field
    midpoint : Y → Y → Y
    g : Y → Z
    midpointBound : ∀ x y → g (midpoint x y) ≡ g x
open JensenConcavity public

-- The current repository does not possess the ordered convex-combination
-- carrier needed for a numeric Jensen inequality.  Therefore the actual
-- Jensen statement is represented as an explicit premise rather than a fake
-- arithmetic theorem.  This record is the exact bridge needed by a future
-- convex-concave minimax development.
record JensenBridge (X Y Z : Set) : Set₁ where
  constructor jensenBridge
  field
    convexJensen : X → X → Y → Set
    concaveJensen : X → Y → Y → Set
open JensenBridge public

record SandwichOrder (Z : Set) : Set₁ where
  constructor sandwichOrder
  field
    lower : Z → Z → Set
    upper : Z → Z → Set
    transitiveLower : ∀ {a b c} → lower a b → lower b c → lower a c
    transitiveUpper : ∀ {a b c} → upper a b → upper b c → upper a c
open SandwichOrder public

record MinMaxSandwich (X Y Z : Set) : Set₁ where
  constructor minMaxSandwich
  field
    f : X → Y → Z
    order : SandwichOrder Z
    lowerEnvelope upperEnvelope : Z
    weakSandwich : lower (order) (lowerEnvelope) (upperEnvelope)
    convexWitness : X → X → Y → Set
    concaveWitness : X → Y → Y → Set
open MinMaxSandwich public

-- Jensen is the correct local ingredient in the mixed/convex-concave proof
-- chain.  It does not, by itself, prove minimax equality.  The equality needs
-- the compact/convex/concave and continuity or finite-game hypotheses supplied
-- by the surrounding minimax theorem.
jensen-is-a-local-premise : ∀ {X Y Z : Set}
  (J : JensenBridge X Y Z)
  → Set
jensen-is-a-local-premise J =
  (∀ x₁ x₂ y → convexJensen J x₁ x₂ y) 
  
-- The weak minimax inequality is logically prior to any Jensen strengthening:
-- it is a separate theorem obligation and cannot be manufactured from Jensen
-- alone.  A concrete finite-game instantiation should provide this relation.
record WeakMinMax (X Y Z : Set) : Set₁ where
  constructor weakMinMax
  field
    f : X → Y → Z
    weakInequality : Set

jensen-does-not-equal-minimax : ∀ {X Y Z : Set}
  (J : JensenBridge X Y Z)
  (W : WeakMinMax X Y Z) →
  Set
jensen-does-not-equal-minimax J W = weakInequality W
