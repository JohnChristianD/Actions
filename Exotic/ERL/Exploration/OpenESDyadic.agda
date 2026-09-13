{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.OpenESDyadic where

open import Data.Fin using (Fin)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; there
  ; here
  ; SelfLoop
  ; Irreducible
  )

-- Finite OpenES theorem surface with explicit fresh one-shot mutation noise.
-- The neutral candidate is represented by choosing the source as the target.
OpenESState : Set
OpenESState = Fin 16

record OpenESNoise : Set where
  constructor openESNoise
  field
    target : OpenESState

open OpenESNoise public

data openESStep : OpenESState → OpenESState → Set where
  openESStepFromFreshNoise : ∀ {s} → (ε : OpenESNoise) → openESStep s (target ε)

openESIrreducibilityProof : Irreducible openESStep
openESIrreducibilityProof s t =
  there (openESStepFromFreshNoise (openESNoise t)) here

openESSelfLoopProof : SelfLoop openESStep
openESSelfLoopProof s = openESStepFromFreshNoise (openESNoise s)
