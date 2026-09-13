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

-- Finite one-shot mutation abstraction: fresh finite noise may select
-- any target state in one exploration tick. This is an abstraction theorem,
-- not a claim that the removed population kernel had the same reachability.
MR15State : Set
MR15State = Fin 16

data MR15Step : MR15State → MR15State → Set where
  stepTo : ∀ {s} t → MR15Step s t

mr15IrreducibilityProof : Irreducible MR15Step
mr15IrreducibilityProof s t = there (stepTo t) here

mr15SelfLoopProof : SelfLoop MR15Step
mr15SelfLoopProof s = stepTo s
