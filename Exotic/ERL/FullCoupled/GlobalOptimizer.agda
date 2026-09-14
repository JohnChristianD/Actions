{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GlobalOptimizer where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; GlobalControl
  ; optimizerToken
  ; global
  ; gruStep
  ; gruGlobalControlPersists
  )
open import Exotic.ERL.FullCoupled.Int8DPG using
  ( DPGActor
  ; DPGCritic
  ; globalActor
  ; globalCritic
  ; DPGCoupled
  ; globalControl
  )

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

record DPGGlobalOptimizerCoherence : Set where
  constructor dpgGlobalOptimizerCoherence
  field
    sharedActorCritic : ∀ (a : DPGActor) (c : DPGCritic) →
      optimizerTokenGlobal a ≡ optimizerTokenGlobal c
  where
    optimizerTokenGlobal : DPGActor → Int8
    optimizerTokenGlobal a = optimizer (globalActor a)
