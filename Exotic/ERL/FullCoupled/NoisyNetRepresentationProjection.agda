{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.NoisyNetRepresentationProjection where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; zero8
  ; one8
  )
open import Exotic.ERL.Finite.Activation using
  ( signReLUQ8
  ; softsignQ8
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
  ; gateParams
  ; NoisyNetStep
  ; noisyNetStepFromFreshNoise
  ; NoisyNetNoise
  ; noisyNetNoise
  )

-- The representation quotient is the pre-softsign signal.  The actual
-- forward observable is then softsignQ8 (signReLUQ8 signal).  GateParams are
-- deliberately omitted from the quotient so the coupled learner theorem has
-- a genuinely larger state space.
SoftsignGatedRepresentationState : Set
SoftsignGatedRepresentationState = Int8

toRepresentation : CoupledNoisyNetState → SoftsignGatedRepresentationState
toRepresentation s = learnerState s

zeroGateParameters : GateParams
zeroGateParameters = gateParams zero8 zero8

fromRepresentation : SoftsignGatedRepresentationState → CoupledNoisyNetState
fromRepresentation x = coupledNoisyNetState zeroGateParameters x

representation-project-lift :
  ∀ x → toRepresentation (fromRepresentation x) ≡ x
representation-project-lift x = refl

softsignGatedForward : SoftsignGatedRepresentationState → Int8
softsignGatedForward x = softsignQ8 (signReLUQ8 x)

softsignGatedForward-law : ∀ x →
  softsignGatedForward x ≡ softsignQ8 (signReLUQ8 x)
softsignGatedForward-law x = refl

softsignGatedStep :
  SoftsignGatedRepresentationState → SoftsignGatedRepresentationState → Set
softsignGatedStep x y =
  NoisyNetStep (fromRepresentation x) (fromRepresentation y)

representation-step-lift :
  ∀ {x y} → softsignGatedStep x y
    → NoisyNetStep (fromRepresentation x) (fromRepresentation y)
representation-step-lift step = step

noisyNetRepresentationIrreducible :
  Irreducible softsignGatedStep
noisyNetRepresentationIrreducible x y =
  there
    (noisyNetStepFromFreshNoise
      (noisyNetNoise zeroGateParameters y))
    here

noisyNetRepresentationSelfLoop :
  SelfLoop softsignGatedStep
noisyNetRepresentationSelfLoop x =
  noisyNetStepFromFreshNoise
    (noisyNetNoise zeroGateParameters x)

noisyNetRepresentationReachability :
  ∀ {s t : CoupledNoisyNetState}
  → Reach NoisyNetStep s t
  → Reach softsignGatedStep
      (toRepresentation s)
      (toRepresentation t)
noisyNetRepresentationReachability here = here
noisyNetRepresentationReachability (there step rest) =
  there step (noisyNetRepresentationReachability rest)

one8≢zero8 : one8 ≡ zero8 → ⊥
one8≢zero8 ()

gateParametersDistinct :
  gateParams zero8 zero8 ≡ gateParams zero8 one8 → ⊥
gateParametersDistinct eq = one8≢zero8 (cong GateParams.sigma3 eq)

hiddenGateSameRepresentation :
  toRepresentation
    (coupledNoisyNetState (gateParams zero8 zero8) zero8)
  ≡
  toRepresentation
    (coupledNoisyNetState (gateParams zero8 one8) zero8)
hiddenGateSameRepresentation = refl

hiddenGateDistinct :
  gateParams zero8 zero8 ≢ gateParams zero8 one8
hiddenGateDistinct eq = gateParametersDistinct eq

-- Genuine strict state extension witness: the softsign-gated quotient has a
-- section into the coupled state, while two distinct coupled gate states have
-- exactly the same projected representation signal.
noisyNetStrictlyStrongerThanRepresentation :
  (∀ x → toRepresentation (fromRepresentation x) ≡ x)
  ×
  (toRepresentation
    (coupledNoisyNetState (gateParams zero8 zero8) zero8)
   ≡
   toRepresentation
    (coupledNoisyNetState (gateParams zero8 one8) zero8))
  ×
  (gateParams zero8 zero8 ≢ gateParams zero8 one8)
noisyNetStrictlyStrongerThanRepresentation =
  representation-project-lift
  , hiddenGateSameRepresentation
  , hiddenGateDistinct
