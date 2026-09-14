{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GlobalL2 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; l2Token
  ; global
  ; gruStep
  )

------------------------------------------------------------------------
-- Global L2 control invariant: the canonical learner carries one global L2
-- coordinate, and recurrent steps do not mutate it.
------------------------------------------------------------------------

record GlobalL2 (s : GRUState) : Set where
  constructor globalL2
  field
    token : Int8
    token-correct : token ≡ l2Token (global s)

open GlobalL2 public

globalL2Witness : ∀ (s : GRUState) → GlobalL2 s
globalL2Witness s = globalL2 (l2Token (global s)) refl

gruStep-preserves-global-L2 :
  ∀ (s : GRUState) (x : Int8) →
  l2Token (global (gruStep s x)) ≡ l2Token (global s)
gruStep-preserves-global-L2 s x = refl
