{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.MR15Reachability where

open import Data.Fin using (Fin)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; there
  ; here
  ; SelfLoop
  ; Irreducible
  )

-- The theorem surface uses a fresh finite one-shot mutation noise. The noise
-- carries the candidate target selected for this tick; this is an explicit
-- finite kernel abstraction, not a claim about a particular continuous law.
MR15State : Set
MR15State = Fin 16

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
