{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GlobalOptimizer where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; optimizerToken
  ; global
  ; gruStep
  )

------------------------------------------------------------------------
-- The optimizer is a global control coordinate, not a method-local state.
------------------------------------------------------------------------

record GlobalOptimizer (s : GRUState) : Set where
  constructor globalOptimizer
  field
    token : Int8
    token-correct : token ≡ optimizerToken (global s)

open GlobalOptimizer public

globalOptimizerWitness : ∀ (s : GRUState) → GlobalOptimizer s
globalOptimizerWitness s = globalOptimizer (optimizerToken (global s)) refl

gruStep-preserves-global-optimizer :
  ∀ (s : GRUState) (x : Int8) →
  optimizerToken (global (gruStep s x)) ≡ optimizerToken (global s)
gruStep-preserves-global-optimizer s x = refl
