{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage06_CoupledLearner where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.DPGInt8 using
  ( GlobalOptimizer
  ; GlobalL2
  ; DPGState
  ; actorForward
  ; criticForward
  ; criticTarget
  ; actorTransport
  ; criticTransport
  )

record CoupledLearner : Set where
  constructor coupledLearner
  field
    state : DPGState
    optimizer : GlobalOptimizer
    globalL2 : GlobalL2

open CoupledLearner public

learnerActor : CoupledLearner → Int8 → Int8
learnerActor c = actorForward (state c)

learnerCritic : CoupledLearner → Int8 → Int8
learnerCritic c = criticForward (state c)

learnerTarget : CoupledLearner → Int8 → Int8 → Int8
learnerTarget c = criticTarget (state c)

actorTransport-law : ∀ c x → actorTransport (state c) x ≡ actorTransport (state c) x
actorTransport-law c x = refl

criticTransport-law : ∀ c x → criticTransport (state c) x ≡ criticTransport (state c) x
criticTransport-law c x = refl
