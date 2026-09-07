{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage05_Representation where

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Representation boundary.
--
-- No standalone representation-level tanh is required. LSTM and GRU own
-- their sigmoid/tanh nonlinearities inside their recurrent transitions.
-- An extra tanh after affine + LayerNorm is therefore an optional model
-- composition, not part of recurrent semantics.
------------------------------------------------------------------------

record Representation (A B : Set) : Set₁ where
  field
    affine : A → B
    layerNorm : B → B

applyRepresentation : ∀ {A B : Set} → Representation A B → A → B
applyRepresentation r x =
  Representation.layerNorm r (Representation.affine r x)

representationBoundary : ∀ {A B : Set} (r : Representation A B) x →
  applyRepresentation r x ≡
    Representation.layerNorm r (Representation.affine r x)
representationBoundary r x = refl
