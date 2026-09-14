{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage06_CoupledLearner where

open import Agda.Builtin.Equality using (_≡_; refl)
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

learnerActor : CoupledLearner → _
learnerActor c = actorForward (state c)

learnerCritic : CoupledLearner → _
learnerCritic c = criticForward (state c)

learnerTarget : CoupledLearner → _
learnerTarget c = criticTarget (state c)

actorTransport-law : ∀ c x → actorTransport (state c) x ≡ actorTransport (state c) x
actorTransport-law c x = refl

criticTransport-law : ∀ c x → criticTransport (state c) x ≡ criticTransport (state c) x
criticTransport-law c x = refl
