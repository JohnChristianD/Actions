{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage05_Representation where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

record Representation (A B : Set) : Set₁ where
  field
    affine : A → B
    layerNorm : B → B
    tanh : B → B

applyRepresentation : ∀ {A B : Set} → Representation A B → A → B
applyRepresentation r x =
  Representation.tanh r (Representation.layerNorm r (Representation.affine r x))

representationBoundary : ∀ {A B : Set} (r : Representation A B) x →
  applyRepresentation r x ≡ Representation.tanh r (Representation.layerNorm r (Representation.affine r x))
representationBoundary r x = refl

finiteVJP : ∀ {A B : Set} → (A → B) → (B → A) → A → B → A
finiteVJP forward pullback x dy = pullback x dy
