{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.MR15Reachability where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁)
open import Exotic.efficient_chad.Int8 using (Int8; zero8)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; there
  ; here
  ; SelfLoop
  ; Irreducible
  )
open import Exotic.ERL.FullCoupled.SoftsignGatedRepresentation using
  ( SoftsignGatedRepresentation )

-- MR15 exploration is defined at the canonical softsign-gated representation
-- boundary rather than at a detached scalar surrogate.
MR15State : Set
MR15State = SoftsignGatedRepresentation

record MR15Noise : Set where
  constructor mr15Noise
  field
    target : MR15State

open MR15Noise public

data MR15Step : MR15State → MR15State → Set where
  stepFromFreshNoise : ∀ {s} → (ε : MR15Noise) → MR15Step s (target ε)

mr15IrreducibilityProof : Irreducible MR15Step
mr15IrreducibilityProof s t =
  there (stepFromFreshNoise (mr15Noise t)) here

mr15SelfLoopProof : SelfLoop MR15Step
mr15SelfLoopProof s = stepFromFreshNoise (mr15Noise s)

-- OpenES is the scalar quotient used only for the strict factor comparison.
openESProjection : MR15State → Int8
openESProjection r = proj₁ r

openESLift : Int8 → MR15State
openESLift x = x , zero8

mr15-openES-retraction :
  ∀ x → openESProjection (openESLift x) ≡ x
mr15-openES-retraction x = refl
