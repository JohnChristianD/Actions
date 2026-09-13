{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.OpenESDyadic where

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

OpenESState : Set
OpenESState = Int8

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

openESSection : Int8 → Int8 × Int8
openESSection x = x , zero8

openESSection-retraction : ∀ x → proj₁ (openESSection x) ≡ x
openESSection-retraction x = refl
