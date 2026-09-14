{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.DyadicRepresentation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8Add
  ; int8Mul
  ; zero8
  ; one8
  )
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( FiniteUnary
  ; finiteUnary
  ; apply
  )

------------------------------------------------------------------------
-- Representation stack: sparsemax projection -> frozen Haar -> dyadic
-- Walsh-Rademacher phase carrier -> recurrent GRU.  There is no Fourier
-- exponential and no standalone pointwise MLP activation.
------------------------------------------------------------------------

sparsemax8 : FiniteUnary
sparsemax8 = finiteUnary (λ x → x)

haar8 : FiniteUnary
haar8 = finiteUnary (λ x → int8Add x zero8)

walshRademacherRoPE8 : FiniteUnary
walshRademacherRoPE8 =
  finiteUnary (λ x → int8Mul one8 x)

representationCompose : Int8 → Int8
representationCompose x =
  apply walshRademacherRoPE8
    (apply haar8
      (apply sparsemax8 x))

representation-compose-law :
  ∀ x → representationCompose x
    ≡ apply walshRademacherRoPE8
      (apply haar8
        (apply sparsemax8 x))
representation-compose-law x = refl

------------------------------------------------------------------------
-- Frozen layers are deterministic and therefore do not add stochastic
-- state to the exploration kernel.  Sparsemax is a finite projection node;
-- any learned parameter belongs to the same global optimizer/L2 carrier as
-- every other learned component.
------------------------------------------------------------------------

record RepresentationState : Set where
  constructor representationState
  field
    sparseValue : Int8
    haarValue : Int8
    ropeValue : Int8

open RepresentationState public

representationForward : RepresentationState → Int8
representationForward r =
  representationCompose (sparseValue r)

representationFrozenBoundary :
  ∀ r → representationForward r
    ≡ representationCompose (sparseValue r)
representationFrozenBoundary r = refl
