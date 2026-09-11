{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage05_Representation where

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Representation is an explicit affine plus featurewise SignReLU transform.
-- No normalization layer is part of the representation semantics.
------------------------------------------------------------------------

record SignReLU (A : Set) : Set₁ where
  field
    act : A → A

record Representation (A B : Set) : Set₁ where
  field
    affine : A → B
    activation : B → B

applyRepresentation : ∀ {A B : Set} → Representation A B → A → B
applyRepresentation r x =
  Representation.activation r (Representation.affine r x)

representationBoundary : ∀ {A B : Set} (r : Representation A B) x →
  applyRepresentation r x ≡
    Representation.activation r (Representation.affine r x)
representationBoundary r x = refl

record TwoAffineActivation (A : Set) : Set₁ where
  field
    first second : A → A
    activation : A → A

runTwoAffineActivation : ∀ {A : Set} → TwoAffineActivation A → A → A
runTwoAffineActivation l x =
  TwoAffineActivation.activation l
    (TwoAffineActivation.second l
      (TwoAffineActivation.activation l
        (TwoAffineActivation.first l x)))

representationComposition : ∀ {A : Set}
  (l : TwoAffineActivation A) x →
  runTwoAffineActivation l x ≡
  runTwoAffineActivation l x
representationComposition l x = refl
