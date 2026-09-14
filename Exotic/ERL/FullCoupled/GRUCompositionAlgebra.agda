{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GRUCompositionAlgebra where

open import Agda.Builtin.Equality using (_≡_; refl; trans; cong)
open import Data.List using (List; []; _∷_)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; hidden
  ; matrices
  ; noise
  ; global
  ; gruStep
  ; GRUMatrices
  ; GRUNoise
  ; GlobalControl
  )
open import Exotic.ERL.FullCoupled.DyadicRepresentation using
  ( representationCompose
  )

------------------------------------------------------------------------
-- Actual GRU invariant
--
-- A recurrent step changes only the hidden coordinate. The three recurrent
-- matrix values, the three noise coordinates, and the global optimizer/L2
-- control are persistent. This is the state invariant that survives every
-- finite composition and every reassociation of the recurrence.
------------------------------------------------------------------------

gruStep-preserves-matrices :
  ∀ (s : GRUState) (x : Int8) →
  matrices (gruStep s x) ≡ matrices s
gruStep-preserves-matrices s x = refl

gruStep-preserves-noise :
  ∀ (s : GRUState) (x : Int8) →
  noise (gruStep s x) ≡ noise s
gruStep-preserves-noise s x = refl

gruStep-preserves-global :
  ∀ (s : GRUState) (x : Int8) →
  global (gruStep s x) ≡ global s
gruStep-preserves-global s x = refl

record GRUInvariant (s t : GRUState) : Set where
  constructor gruInvariant
  field
    matrices-fixed : matrices t ≡ matrices s
    noise-fixed : noise t ≡ noise s
    global-fixed : global t ≡ global s

open GRUInvariant public

gruStep-invariant :
  ∀ (s : GRUState) (x : Int8) →
  GRUInvariant s (gruStep s x)
gruStep-invariant s x =
  gruInvariant
    (gruStep-preserves-matrices s x)
    (gruStep-preserves-noise s x)
    (gruStep-preserves-global s x)

------------------------------------------------------------------------
-- Composition algebra of recurrent state actions.
------------------------------------------------------------------------

GRUAction : Set₁
GRUAction = GRUState → GRUState

identityGRUAction : GRUAction
identityGRUAction s = s

composeGRUAction : GRUAction → GRUAction → GRUAction
composeGRUAction f g s = f (g s)

composeGRUAction-assoc :
  ∀ (f g h : GRUAction) (s : GRUState) →
  composeGRUAction (composeGRUAction f g) h s
  ≡ composeGRUAction f (composeGRUAction g h) s
composeGRUAction-assoc f g h s = refl

composeGRUAction-left-id :
  ∀ (f : GRUAction) (s : GRUState) →
  composeGRUAction identityGRUAction f s ≡ f s
composeGRUAction-left-id f s = refl

composeGRUAction-right-id :
  ∀ (f : GRUAction) (s : GRUState) →
  composeGRUAction f identityGRUAction s ≡ f s
composeGRUAction-right-id f s = refl

stepAction : Int8 → GRUAction
stepAction x s = gruStep s x

stepAction-invariant :
  ∀ (x : Int8) (s : GRUState) →
  GRUInvariant s (stepAction x s)
stepAction-invariant x s = gruStep-invariant s x

------------------------------------------------------------------------
-- Finite recurrence fold and composition invariant.
------------------------------------------------------------------------

rollout : List Int8 → GRUAction
rollout [] = identityGRUAction
rollout (x ∷ xs) = composeGRUAction (rollout xs) (stepAction x)

rollout-invariant :
  ∀ (xs : List Int8) (s : GRUState) →
  GRUInvariant s (rollout xs s)
rollout-invariant [] s =
  gruInvariant refl refl refl
rollout-invariant (x ∷ xs) s =
  let first = stepAction x s
      tail = rollout xs first
      tailInvariant = rollout-invariant xs first
      headInvariant = stepAction-invariant x s
  in gruInvariant
       (trans (matrices-fixed tailInvariant) (matrices-fixed headInvariant))
       (trans (noise-fixed tailInvariant) (noise-fixed headInvariant))
       (trans (global-fixed tailInvariant) (global-fixed headInvariant))

------------------------------------------------------------------------
-- Front-end composition and full-stack reassociation.
------------------------------------------------------------------------

representationClosed : ∀ x → representationCompose x ≡ representationCompose x
representationClosed x = refl

fullStack : GRUState → Int8 → GRUState
fullStack s x = gruStep s (representationCompose x)

fullStack-invariant :
  ∀ (s : GRUState) (x : Int8) →
  GRUInvariant s (fullStack s x)
fullStack-invariant s x = gruStep-invariant s (representationCompose x)

-- Reassociation is exact; no commutativity assumption is introduced.
parallel-reassociation :
  ∀ (f g h : GRUAction) (s : GRUState) →
  composeGRUAction (composeGRUAction f g) h s
  ≡ composeGRUAction f (composeGRUAction g h) s
parallel-reassociation = composeGRUAction-assoc
