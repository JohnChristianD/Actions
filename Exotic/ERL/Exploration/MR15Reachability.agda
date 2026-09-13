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
  ( SoftsignGatedRepresentation
  ; SoftsignGatedStep
  ; softsignTarget
  )

MR15State : Set
MR15State = SoftsignGatedRepresentation

MR15Step : MR15State → MR15State → Set
MR15Step = SoftsignGatedStep

mr15IrreducibilityProof : Irreducible MR15Step
mr15IrreducibilityProof s t = there (softsignTarget t) here

mr15SelfLoopProof : SelfLoop MR15Step
mr15SelfLoopProof s = softsignTarget s

-- OpenES is the scalar quotient used for the strict factor comparison.
openESProjection : MR15State → Int8
openESProjection = proj₁

openESLift : Int8 → MR15State
openESLift x = x , zero8

mr15-openES-retraction :
  ∀ x → openESProjection (openESLift x) ≡ x
mr15-openES-retraction x = refl
