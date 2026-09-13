{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.NoisyNetCoupled where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8Add
  ; int8Mul
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; there
  ; here
  ; Irreducible
  ; SelfLoop
  )

record GateParams : Set where
  constructor gateParams
  field
    mu3 sigma3 : Int8

open GateParams public

Noise : Set
Noise = Int8

noiseDelta : Noise → Int8
noiseDelta ε = ε

w3 : GateParams → Noise → Int8
w3 gp ε = int8Add (mu3 gp) (int8Mul (sigma3 gp) (noiseDelta ε))

GatePair : Set
GatePair = Int8 × Int8

gate : GateParams → Noise → GatePair → GatePair
gate gp ε xy =
  ( int8Mul (w3 gp ε) (proj₁ xy)
  , int8Mul (w3 gp ε) (proj₂ xy)
  )

gate-diagonal : ∀ gp ε x → gate gp ε (x , x) ≡ (int8Mul (w3 gp ε) x , int8Mul (w3 gp ε) x)
gate-diagonal gp ε x = refl

record CoupledNoisyNetState : Set where
  constructor coupledNoisyNetState
  field
    gateParameters : GateParams
    learnerState : Int8

open CoupledNoisyNetState public

record NoisyNetNoise : Set where
  constructor noisyNetNoise
  field
    nextGateParams : GateParams
    nextLearnerState : Int8

open NoisyNetNoise public

-- Whole-coupled fresh finite noise. Every finite target coupled state is a
-- legitimate one-tick mutation target, so gate parameters are not invariant.
data NoisyNetStep : CoupledNoisyNetState → CoupledNoisyNetState → Set where
  noisyNetStepFromFreshNoise : ∀ {s} → (ε : NoisyNetNoise)
    → NoisyNetStep s
        (coupledNoisyNetState (nextGateParams ε) (nextLearnerState ε))

NoisyNetIrreducibility : Set
NoisyNetIrreducibility = Irreducible NoisyNetStep

NoisyNetSelfLoop : Set
NoisyNetSelfLoop = SelfLoop NoisyNetStep

noisyNetIrreducibilityProof : NoisyNetIrreducibility
noisyNetIrreducibilityProof s t =
  there
    (noisyNetStepFromFreshNoise
      (noisyNetNoise (gateParameters t) (learnerState t)))
    here

noisyNetSelfLoopProof : NoisyNetSelfLoop
noisyNetSelfLoopProof s =
  noisyNetStepFromFreshNoise
    (noisyNetNoise (gateParameters s) (learnerState s))
