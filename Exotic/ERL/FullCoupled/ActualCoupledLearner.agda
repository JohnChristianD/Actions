{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ActualCoupledLearner where

open import Exotic.efficient_chad.Int8 using (Int8; zero8; one8; int8OfNat)
open import Exotic.ERL.Finite.Int8Vector using (Int8Vector4; vec4)
open import Exotic.ERL.Finite.TrueOnlineTD using (TrueOnlineState; initialState; tdError)
open import Exotic.ERL.Finite.ComposedLearner using (composedSoftsignStep)
open import Exotic.ERL.FullCoupled.F4IntKernel using (F4State; zeroF4; stepF4; theta)
open import Exotic.ERL.FullCoupled.SharedActorCritic using
  ( ActorCriticParameters
  ; sampleSharedParameters
  ; actorForward
  ; criticForward
  ; sampleWindow
  )

record State : Set where
  constructor state
  field
    network : ActorCriticParameters
    a b c d e o : F4State
    critic : TrueOnlineState
    actorOutput criticOutput : Int8
open State public

start : State
start = state
  sampleSharedParameters
  zeroF4 zeroF4 zeroF4 zeroF4 zeroF4 zeroF4
  initialState
  (actorForward sampleSharedParameters sampleWindow)
  (criticForward sampleSharedParameters sampleWindow)

step : Int8 → Int8Vector4 → Int8Vector4 → State → State
step r phi nextPhi s =
  let g = tdError r phi nextPhi (critic s)
      c' = composedSoftsignStep r phi nextPhi (critic s)
      actor' = actorForward (network s) sampleWindow
      critic' = criticForward (network s) sampleWindow
  in state
    (network s)
    (stepF4 g (a s))
    (stepF4 g (b s))
    (stepF4 g (c s))
    (stepF4 g (d s))
    (stepF4 g (e s))
    (stepF4 g (o s))
    c'
    actor'
    critic'

unitFeature : Int8Vector4
unitFeature = vec4 one8 zero8 zero8 zero8

learningWitness : State
learningWitness = step (int8OfNat 5) unitFeature unitFeature start

learningWitness-law : theta (a learningWitness) = one8
learningWitness-law = refl
