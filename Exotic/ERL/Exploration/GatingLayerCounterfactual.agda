{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.GatingLayerCounterfactual where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; here
  ; there
  )

record GatingFactorization (Full Gate : Set) where
  field
    project : Full → Gate
    lift : Gate → Full

    project-lift : ∀ g → project (lift g) ≡ g

    GateStep : Gate → Gate → Set
    FullStep : Full → Full → Set

    lift-step : ∀ {g h} → GateStep g h → FullStep (lift g) (lift h)

open GatingFactorization public

-- Counterfactual theorem: if exploration is restricted to a gate relation
-- and every gate transition has a full-state lift, gate reachability lifts
-- to reachability inside the image of `lift`. This says nothing about
-- arbitrary learner/EA states outside that image.
gate-reach-lifts : ∀ {Full Gate : Set}
  (F : GatingFactorization Full Gate)
  {g h : Gate}
  → Reach (GateStep F) g h
  → Reach (FullStep F) (lift F g) (lift F h)
gate-reach-lifts F here = here
gate-reach-lifts F (there step rest) =
  there (lift-step F step) (gate-reach-lifts F rest)

-- The gate representation is faithfully embedded by the chosen lift.
project-after-lift : ∀ {Full Gate : Set}
  (F : GatingFactorization Full Gate)
  → ∀ g → project F (lift F g) ≡ g
project-after-lift F = project-lift F
