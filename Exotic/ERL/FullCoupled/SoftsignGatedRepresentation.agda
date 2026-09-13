{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SoftsignGatedRepresentation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Exotic.efficient_chad.Int8 using (Int8; zero8)
open import Exotic.efficient_chad.SoftsignGatedComposition using
  ( softsignGatedForwardLaw-proof
  ; softsignGatedPullbackLaw-proof
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using (there; here)
open import Exotic.ERL.FullCoupled.NoisyNetCoupled using
  ( GateParams
  ; mu3
  ; CoupledNoisyNetState
  ; coupledNoisyNetState
  ; gateParameters
  ; learnerState
  ; NoisyNetStep
  ; noisyNetStepFromFreshNoise
  ; NoisyNetNoise
  ; noisyNetNoise
  )

-- Canonical exploration boundary: the two finite coordinates entering the
-- gated representation are observable; sigma3 remains a coupled hidden
-- learner coordinate and therefore supplies the strict state extension.
SoftsignGatedRepresentation : Set
SoftsignGatedRepresentation = Int8 × Int8

projectSoftsignGated : CoupledNoisyNetState → SoftsignGatedRepresentation
projectSoftsignGated s = mu3 (gateParameters s) , learnerState s

liftSoftsignGated : SoftsignGatedRepresentation → CoupledNoisyNetState
liftSoftsignGated r = coupledNoisyNetState (gateParams (proj₁ r) zero8) (proj₂ r)
  where
  gateParams : Int8 → Int8 → GateParams
  gateParams = NoisyNetCoupled.gateParams

softsignGated-retraction :
  ∀ r → projectSoftsignGated (liftSoftsignGated r) ≡ r
softsignGated-retraction r = refl

-- The representation-layer exploration relation is a fresh finite target
-- relation on the exact softsign-gated boundary state.
data SoftsignGatedStep : SoftsignGatedRepresentation → SoftsignGatedRepresentation → Set where
  softsignTarget : ∀ {s} → (r : SoftsignGatedRepresentation)
    → SoftsignGatedStep s r

project-noisyNet-step : ∀ {s t}
  → NoisyNetStep s t
  → SoftsignGatedStep (projectSoftsignGated s) (projectSoftsignGated t)
project-noisyNet-step (noisyNetStepFromFreshNoise ε) =
  softsignTarget (projectSoftsignGated
    (coupledNoisyNetState (NoisyNetNoise.nextGateParams ε)
      (NoisyNetNoise.nextLearnerState ε)))

lift-softsign-step : ∀ {r q}
  → SoftsignGatedStep r q
  → NoisyNetStep (liftSoftsignGated r) (liftSoftsignGated q)
lift-softsign-step (softsignTarget q) =
  noisyNetStepFromFreshNoise
    (noisyNetNoise
      (NoisyNetCoupled.gateParams (proj₁ q) zero8)
      (proj₂ q))

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

-- The forward/pullback composition is part of the same representation-boundary
-- theorem surface; these names are imported by the full-coupling composition.
softsignGatedForward-composed = softsignGatedForwardLaw-proof
softsignGatedPullback-composed = softsignGatedPullbackLaw-proof
