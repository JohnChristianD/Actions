{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SoftsignGatedRepresentation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.NoisyNetCoupled using
  ( GateParams
  ; CoupledNoisyNetState
  ; coupledNoisyNetState
  ; gateParameters
  ; learnerState
  )

-- The representation interface exposed to the forward activation chain
-- carries the mutable gate parameters together with the learner signal.
-- The concrete signReLU8/softsign8 operators are composed separately by
-- Exotic.efficient_chad.SoftsignGatedComposition.
SoftsignGatedRepresentation : Set
SoftsignGatedRepresentation = GateParams × Int8

projectSoftsignGated : CoupledNoisyNetState → SoftsignGatedRepresentation
projectSoftsignGated s = gateParameters s , learnerState s

liftSoftsignGated : SoftsignGatedRepresentation → CoupledNoisyNetState
liftSoftsignGated r = coupledNoisyNetState (proj₁ r) (proj₂ r)

softsignGated-retraction :
  ∀ r → projectSoftsignGated (liftSoftsignGated r) ≡ r
softsignGated-retraction r = refl

record RepresentationRetraction {S R : Set} : Set₁ where
  constructor representationRetraction
  field
    project : S → R
    lift : R → S
    retract : ∀ r → project (lift r) ≡ r

noisyNetSoftsignRetraction : RepresentationRetraction
noisyNetSoftsignRetraction =
  representationRetraction
    projectSoftsignGated
    liftSoftsignGated
    softsignGated-retraction
