{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.OpenESDyadic where

open import Data.Fin using (Fin)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; there
  ; here
  ; SelfLoop
  ; Irreducible
  )

-- Finite OpenES abstraction with fresh antithetic/neutral finite mutation.
-- One tick may select any finite candidate state; neutral selection gives
-- an actual self-loop.
OpenESState : Set
OpenESState = Fin 16

data openESStep : OpenESState → OpenESState → Set where
  openESStepTo : ∀ {s} t → openESStep s t

openESIrreducibilityProof : Irreducible openESStep
openESIrreducibilityProof s t = there (openESStepTo t) here

openESSelfLoopProof : SelfLoop openESStep
openESSelfLoopProof s = openESStepTo s
