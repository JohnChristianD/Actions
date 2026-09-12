{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage05_Representation where

------------------------------------------------------------------------
-- Representation semantics are the pre-recurrent feature transform.
-- There is deliberately no standalone representation-level tanh layer:
-- recurrent cells own their nonlinearities, and any output nonlinearity is
-- an explicit head in the shared CHAD network.
------------------------------------------------------------------------

record Representation (A B : Set) : Set₁ where
  field
    affine : A → B
    layerNorm : B → B

applyRepresentation : ∀ {A B : Set} → Representation A B → A → B
applyRepresentation r x =
  Representation.layerNorm r (Representation.affine r x)
