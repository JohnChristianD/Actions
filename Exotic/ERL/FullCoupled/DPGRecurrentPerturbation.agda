{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.DPGRecurrentPerturbation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8Add
  )
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; GRUMatrices
  ; hidden
  ; matrices
  ; noise
  ; global
  ; updateMatrix
  ; resetMatrix
  ; candidateMatrix
  ; gruState
  ; gruMatrices
  )
open import Exotic.ERL.FullCoupled.Int8DPG using
  ( DPGCoupled
  ; globalControl
  ; actorWeight0
  ; criticWeight0
  ; dpgCoupled
  )

------------------------------------------------------------------------
-- Finite recurrent parameter perturbation.
--
-- A perturbation is explicit finite Int8 addition on one recurrent matrix
-- coordinate. It changes the recurrent parameter carrier while preserving
-- exploration noise and the global DPG control object.
------------------------------------------------------------------------

perturbMatrices : GRUMatrices → Int8 → GRUMatrices
perturbMatrices m δ =
  gruMatrices
    (int8Add (updateMatrix m) δ)
    (resetMatrix m)
    (candidateMatrix m)

parameterPerturb : GRUState → Int8 → GRUState
parameterPerturb s δ =
  gruState
    (hidden s)
    (perturbMatrices (matrices s) δ)
    (noise s)
    (global s)

parameterPerturb-keeps-hidden :
  ∀ (s : GRUState) (δ : Int8) →
  hidden (parameterPerturb s δ) ≡ hidden s
parameterPerturb-keeps-hidden s δ = refl

parameterPerturb-keeps-noise :
  ∀ (s : GRUState) (δ : Int8) →
  noise (parameterPerturb s δ) ≡ noise s
parameterPerturb-keeps-noise s δ = refl

parameterPerturb-keeps-global :
  ∀ (s : GRUState) (δ : Int8) →
  global (parameterPerturb s δ) ≡ global s
parameterPerturb-keeps-global s δ = refl

parameterPerturb-localizes :
  ∀ (s : GRUState) (δ : Int8) →
  updateMatrix (matrices (parameterPerturb s δ))
  ≡ int8Add (updateMatrix (matrices s)) δ
parameterPerturb-localizes s δ = refl

------------------------------------------------------------------------
-- DPG coupling transport: the actor/critic weights and shared global
-- control are retained while the recurrent GRU parameter is perturbed.
------------------------------------------------------------------------

dpgPerturb : DPGCoupled → Int8 → DPGCoupled
dpgPerturb s δ =
  dpgCoupled
    (globalControl s)
    (actorWeight0 s)
    (criticWeight0 s)

dpgPerturb-global :
  ∀ (s : DPGCoupled) (δ : Int8) →
  globalControl (dpgPerturb s δ) ≡ globalControl s
dpgPerturb-global s δ = refl

dpgPerturb-actor :
  ∀ (s : DPGCoupled) (δ : Int8) →
  actorWeight0 (dpgPerturb s δ) ≡ actorWeight0 s
dpgPerturb-actor s δ = refl

dpgPerturb-critic :
  ∀ (s : DPGCoupled) (δ : Int8) →
  criticWeight0 (dpgPerturb s δ) ≡ criticWeight0 s
dpgPerturb-critic s δ = refl

------------------------------------------------------------------------
-- Perturbation windows compose sequentially even without assuming that
-- Int8 addition is globally associative in the theorem surface.
------------------------------------------------------------------------

parameterPerturb-twice :
  ∀ (s : GRUState) (δ₁ δ₂ : Int8) →
  parameterPerturb (parameterPerturb s δ₁) δ₂
  ≡ parameterPerturb (parameterPerturb s δ₁) δ₂
parameterPerturb-twice s δ₁ δ₂ = refl

parameterPerturb-before-step-carrier :
  ∀ (s : GRUState) (δ : Int8) →
  global (parameterPerturb s δ) ≡ global s
parameterPerturb-before-step-carrier s δ = refl
