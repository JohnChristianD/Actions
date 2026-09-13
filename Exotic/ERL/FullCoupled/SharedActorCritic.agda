{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.SharedActorCritic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_)
open import Exotic.efficient_chad.Int8 using (Int8; int8Add; int8Mul; zero8; one8)
open import Exotic.ERL.FullCoupled.FiniteLearner using
  ( Parameters
  ; Token
  ; Window2
  ; attentionStep
  ; ffn1
  ; ffn2
  ; fixedFastfood2
  ; softsign8
  ; qε
  ; Parameters.w5
  ; token
  ; window2
  ; parameters
  )

sharedRepresentation : Parameters → Window2 → Int8
sharedRepresentation p w =
  let h = attentionStep (Window2.previous w) (Window2.current w)
      a = ffn1 p h
      uv = fixedFastfood2 (a , h)
      u = Data.Product.proj₁ uv
      v = Data.Product.proj₂ uv
      b = int8Add (ffn2 p u) v
      g = softsign8 (int8Mul (Parameters.w5 p) b)
  in qε 3 g

record ActorCriticParameters : Set where
  constructor actorCriticParameters
  field
    shared actorHeadScale actorHeadBias : Int8
    criticHeadScale criticHeadBias : Int8

open ActorCriticParameters public

sharedParameters : ActorCriticParameters → Parameters
sharedParameters _ = parameters one8 one8 one8 one8 one8 one8

actorForward : ActorCriticParameters → Window2 → Int8
actorForward p w = int8Add
  (int8Mul (actorHeadScale p) (sharedRepresentation (sharedParameters p) w))
  (actorHeadBias p)

criticForward : ActorCriticParameters → Window2 → Int8
criticForward p w = int8Add
  (int8Mul (criticHeadScale p) (sharedRepresentation (sharedParameters p) w))
  (criticHeadBias p)

sharedActorCriticAgreement : ∀ (p : ActorCriticParameters) (w : Window2) →
  sharedRepresentation (sharedParameters p) w ≡
  sharedRepresentation (sharedParameters p) w
sharedActorCriticAgreement p w = refl

sampleSharedParameters : ActorCriticParameters
sampleSharedParameters = actorCriticParameters
  one8
  one8
  zero8
  one8
  zero8

sampleWindow : Window2
sampleWindow = window2
  (token one8 zero8 zero8 one8)
  (token one8 zero8 zero8 one8)

sampleActorOutput : Int8
sampleActorOutput = actorForward sampleSharedParameters sampleWindow

sampleCriticOutput : Int8
sampleCriticOutput = criticForward sampleSharedParameters sampleWindow
