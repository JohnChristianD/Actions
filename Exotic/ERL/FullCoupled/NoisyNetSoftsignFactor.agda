{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.NoisyNetSoftsignFactor where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Exotic.efficient_chad.Int8 using (Int8; zero8)
open import Exotic.ERL.FullCoupled.NoisyNetCoupled using
  ( GateParams
  ; gateParams
  ; mu3
  ; CoupledNoisyNetState
  ; coupledNoisyNetState
  ; gateParameters
  ; learnerState
  ; NoisyNetStep
  ; noisyNetStepFromFreshNoise
  ; NoisyNetNoise
  )
open import Exotic.ERL.FullCoupled.SoftsignGatedRepresentation using
  ( SoftsignGatedRepresentation
  ; SoftsignGatedStep
  ; softsignTarget
  )

projectSoftsignGated : CoupledNoisyNetState → SoftsignGatedRepresentation
projectSoftsignGated s = mu3 (gateParameters s) , learnerState s

liftSoftsignGated : SoftsignGatedRepresentation → CoupledNoisyNetState
liftSoftsignGated r = coupledNoisyNetState (gateParams (proj₁ r) zero8) (proj₂ r)

softsignGated-retraction :
  ∀ r → projectSoftsignGated (liftSoftsignGated r) ≡ r
softsignGated-retraction r = refl

project-noisyNet-step : ∀ {s t}
  → NoisyNetStep s t
  → SoftsignGatedStep (projectSoftsignGated s) (projectSoftsignGated t)
project-noisyNet-step (noisyNetStepFromFreshNoise ε) =
  softsignTarget
    (projectSoftsignGated
      (coupledNoisyNetState
        (NoisyNetNoise.nextGateParams ε)
        (NoisyNetNoise.nextLearnerState ε)))

lift-softsign-step : ∀ {r q}
  → SoftsignGatedStep r q
  → NoisyNetStep (liftSoftsignGated r) (liftSoftsignGated q)
lift-softsign-step (softsignTarget q) =
  noisyNetStepFromFreshNoise
    (noisyNetNoise (gateParams (proj₁ q) zero8) (proj₂ q))

record RepresentationFactor {S R : Set}
    (stepS : S → S → Set) (stepR : R → R → Set) : Set₁ where
  constructor representationFactor
  field
    project : S → R
    lift : R → S
    retract : ∀ r → project (lift r) ≡ r
    projectStep : ∀ {s t} → stepS s t → stepR (project s) (project t)
    liftStep : ∀ {r q} → stepR r q → stepS (lift r) (lift q)

noisyNetSoftsignFactor :
  RepresentationFactor NoisyNetStep SoftsignGatedStep
noisyNetSoftsignFactor =
  representationFactor
    projectSoftsignGated
    liftSoftsignGated
    softsignGated-retraction
    project-noisyNet-step
    lift-softsign-step
