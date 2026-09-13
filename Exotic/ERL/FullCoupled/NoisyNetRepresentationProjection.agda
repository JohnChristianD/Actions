{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.NoisyNetRepresentationProjection where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.efficient_chad.SoftsignGatedComposition using
  ( SoftsignGatedForward
  ; softsignGatedOperator
  ; primal
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; there
  ; here
  ; Irreducible
  ; SelfLoop
  )
open import Exotic.ERL.FullCoupled.NoisyNetCoupled using
  ( CoupledNoisyNetState
  ; coupledNoisyNetState
  ; gateParameters
  ; learnerState
  ; GateParams
  ; NoisyNetStep
  ; noisyNetStepFromFreshNoise
  ; NoisyNetNoise
  ; noisyNetNoise
  )

record SoftsignGatedRepresentationState : Set where
  constructor softsignGatedRepresentationState
  field
    representationGate : GateParams
    representationSignal : Int8

open SoftsignGatedRepresentationState public

toRepresentation : CoupledNoisyNetState → SoftsignGatedRepresentationState
toRepresentation s =
  softsignGatedRepresentationState
    (gateParameters s)
    (learnerState s)

fromRepresentation : SoftsignGatedRepresentationState → CoupledNoisyNetState
fromRepresentation r =
  coupledNoisyNetState
    (representationGate r)
    (representationSignal r)

representation-project-lift :
  ∀ r → toRepresentation (fromRepresentation r) ≡ r
representation-project-lift r = refl

representation-lift-project :
  ∀ s → fromRepresentation (toRepresentation s) ≡ s
representation-lift-project s = refl

SoftsignGatedOutput : SoftsignGatedForward → CoupledNoisyNetState → Int8
SoftsignGatedOutput f s =
  primal (softsignGatedOperator f) (learnerState s)

NoisyNetRepresentationStep :
  SoftsignGatedRepresentationState → SoftsignGatedRepresentationState → Set
NoisyNetRepresentationStep r r' =
  NoisyNetStep (fromRepresentation r) (fromRepresentation r')

representation-step-lift :
  ∀ {r r'} → NoisyNetRepresentationStep r r'
    → NoisyNetStep (fromRepresentation r) (fromRepresentation r')
representation-step-lift step = step

noisyNetRepresentationIrreducible :
  Irreducible NoisyNetRepresentationStep
noisyNetRepresentationIrreducible r r' =
  there
    (noisyNetStepFromFreshNoise
      (noisyNetNoise
        (representationGate r')
        (representationSignal r')))
    here

noisyNetRepresentationSelfLoop :
  SelfLoop NoisyNetRepresentationStep
noisyNetRepresentationSelfLoop r =
  noisyNetStepFromFreshNoise
    (noisyNetNoise
      (representationGate r)
      (representationSignal r))

noisyNetRepresentationReachability :
  ∀ {s t : CoupledNoisyNetState}
  → Reach NoisyNetStep s t
  → Reach NoisyNetRepresentationStep
      (toRepresentation s)
      (toRepresentation t)
noisyNetRepresentationReachability here = here
noisyNetRepresentationReachability (there step rest) =
  there step (noisyNetRepresentationReachability rest)
