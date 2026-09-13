{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.NoisyNetSoftsignLift where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; zero8
  ; one8
  )
open import Exotic.ERL.Finite.Activation using
  ( softsignQ8
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; there
  ; here
  )
open import Exotic.ERL.FullCoupled.NoisyNetCoupled using
  ( GateParams
  ; gateParams
  ; CoupledNoisyNetState
  ; coupledNoisyNetState
  ; gateParameters
  ; learnerState
  ; NoisyNetStep
  ; noisyNetStepFromFreshNoise
  )

-- Representation coordinate at the softsign boundary.  The gate parameters
-- remain hidden from this quotient, while the pre-softsign Int8 coordinate is
-- what the forward activation consumes.
SoftsignGatedState : Set
SoftsignGatedState = Int8

softsignProjection : CoupledNoisyNetState → SoftsignGatedState
softsignProjection s = learnerState s

softsignGatedForward : SoftsignGatedState → Int8
softsignGatedForward x = softsignQ8 x

softsignGatedValue : CoupledNoisyNetState → Int8
softsignGatedValue s = softsignQ8 (softsignProjection s)

zeroGateParameters : GateParams
zeroGateParameters = gateParams zero8 zero8

softsignLift : SoftsignGatedState → CoupledNoisyNetState
softsignLift x = coupledNoisyNetState zeroGateParameters x

projection-lift : ∀ x → softsignProjection (softsignLift x) ≡ x
projection-lift x = refl

SoftsignGatedStep : SoftsignGatedState → SoftsignGatedState → Set
SoftsignGatedStep x y =
  NoisyNetStep (softsignLift x) (softsignLift y)

softsignReachFromNoisyNet : ∀ {s t} → Reach NoisyNetStep s t
  → Reach SoftsignGatedStep (softsignProjection s) (softsignProjection t)
softsignReachFromNoisyNet here = here
softsignReachFromNoisyNet (there step rest) =
  there step (softsignReachFromNoisyNet rest)

noisyNetReachFromSoftsign : ∀ {x y} → Reach SoftsignGatedStep x y
  → Reach NoisyNetStep (softsignLift x) (softsignLift y)
noisyNetReachFromSoftsign here = here
noisyNetReachFromSoftsign (there step rest) =
  there step (noisyNetReachFromSoftsign rest)

one8≢zero8 : one8 ≡ zero8 → ⊥
one8≢zero8 ()

gateParametersDistinct :
  gateParams zero8 zero8 ≡ gateParams zero8 one8 → ⊥
gateParametersDistinct eq = one8≢zero8 (cong GateParams.sigma3 eq)

hiddenGateWitness :
  softsignProjection
    (coupledNoisyNetState (gateParams zero8 zero8) zero8)
  ≡
  softsignProjection
    (coupledNoisyNetState (gateParams zero8 one8) zero8)
hiddenGateWitness = refl

hiddenGateSeparates :
  gateParams zero8 zero8 ≢ gateParams zero8 one8
hiddenGateSeparates eq = gateParametersDistinct eq

-- The quotient has an exact projection/lift section, while the coupled state
-- retains a mutable gate coordinate not represented by the softsign scalar.
noisyNetStrictlyExtendsSoftsign : Set
noisyNetStrictlyExtendsSoftsign =
  (∀ x → softsignProjection (softsignLift x) ≡ x)
  ×
  (softsignProjection
    (coupledNoisyNetState (gateParams zero8 zero8) zero8)
   ≡
   softsignProjection
    (coupledNoisyNetState (gateParams zero8 one8) zero8))
  ×
  (gateParams zero8 zero8 ≢ gateParams zero8 one8)

noisyNetStrictlyExtendsSoftsign-proof : noisyNetStrictlyExtendsSoftsign
noisyNetStrictlyExtendsSoftsign-proof =
  projection-lift
  , hiddenGateWitness
  , hiddenGateSeparates
