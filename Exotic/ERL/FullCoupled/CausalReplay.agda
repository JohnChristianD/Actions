{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CausalReplay where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Exotic.efficient_chad.Int8 using (Int8; zero8)
open import Exotic.ERL.Finite.Int8Vector using (Int8Vector4; vec4)
open import Exotic.ERL.FullCoupled.ActualCoupledLearner using (State; start; step)

record Transition : Set where
  constructor transition
  field
    reward : Int8
    phi : Int8Vector4
    nextPhi : Int8Vector4

open Transition public

replay : List Transition → State → State
replay [] s = s
replay (t ∷ ts) s =
  replay ts (step (reward t) (phi t) (nextPhi t) s)

singleReplay : ∀ (t : Transition) (s : State) →
  replay (t ∷ []) s ≡ step (reward t) (phi t) (nextPhi t) s
singleReplay t s = refl

zeroFeature : Int8Vector4
zeroFeature = vec4 zero8 zero8 zero8 zero8

zeroTransition : Transition
zeroTransition = transition zero8 zeroFeature zeroFeature

causal-zero-self-loop : replay (zeroTransition ∷ []) start ≡ start
causal-zero-self-loop = refl
