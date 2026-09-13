{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.SharedActorCritic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8Add
  ; int8Mul
  ; zero8
  ; one8
  )
open import Exotic.ERL.FullCoupled.FiniteLearner using
  ( Parameters
  ; Window2
  ; parameters
  ; learnForward
  )

record SharedActorCriticParameters : Set where
  constructor sharedParameters
  field
    representationParameters : Parameters
    actorScale actorBias : Int8
    criticScale criticBias : Int8

open SharedActorCriticParameters public

sharedRepresentation : SharedActorCriticParameters → Window2 → Int8
sharedRepresentation p w =
  learnForward (representationParameters p) w

actorRepresentation : SharedActorCriticParameters → Window2 → Int8
actorRepresentation = sharedRepresentation

criticRepresentation : SharedActorCriticParameters → Window2 → Int8
criticRepresentation = sharedRepresentation

actorHead : SharedActorCriticParameters → Window2 → Int8
actorHead p w = int8Add
  (int8Mul (actorScale p) (sharedRepresentation p w))
  (actorBias p)

criticHead : SharedActorCriticParameters → Window2 → Int8
criticHead p w = int8Add
  (int8Mul (criticScale p) (sharedRepresentation p w))
  (criticBias p)

sharedRepresentation-law : ∀ (p : SharedActorCriticParameters) (w : Window2) →
  actorRepresentation p w ≡ criticRepresentation p w
sharedRepresentation-law p w = refl

sampleSharedParameters : SharedActorCriticParameters
sampleSharedParameters = sharedParameters
  (parameters one8 one8 one8 one8 one8 one8)
  one8
  zero8
  one8
  zero8

sampleSharedRepresentation : Window2 → Int8
sampleSharedRepresentation = sharedRepresentation sampleSharedParameters

sampleActorOutput : Window2 → Int8
sampleActorOutput = actorHead sampleSharedParameters

sampleCriticOutput : Window2 → Int8
sampleCriticOutput = criticHead sampleSharedParameters
