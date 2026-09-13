{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.NoisyNetRepresentationProjection where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
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
  ; PeriodOne
  ; periodOne-from-components
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
  ; noisyNetIrreducibilityProof
  ; noisyNetSelfLoopProof
  )

-- The representation quotient is the pre-softsign signal. The actual forward
-- observable is softsignQ8 (signReLUQ8 signal). GateParams are omitted from
-- the quotient, so the coupled learner theorem has a genuinely larger state.
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

representation-step-project :
  ∀ {s t} → NoisyNetStep s t
    → softsignGatedStep (toRepresentation s) (toRepresentation t)
representation-step-project step = step

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

noisyNetRepresentationPeriodOne :
  PeriodOne softsignGatedStep
noisyNetRepresentationPeriodOne =
  periodOne-from-components
    noisyNetRepresentationIrreducible
    noisyNetRepresentationSelfLoop

noisyNetRepresentationReachability :
  ∀ {s t : CoupledNoisyNetState}
  → Reach NoisyNetStep s t
  → Reach softsignGatedStep
      (toRepresentation s)
      (toRepresentation t)
noisyNetRepresentationReachability here = here
noisyNetRepresentationReachability (there step rest) =
  there (representation-step-project step)
    (noisyNetRepresentationReachability rest)

noisyNetCoupledReachability :
  ∀ s t → Reach NoisyNetStep s t
noisyNetCoupledReachability = noisyNetIrreducibilityProof

noisyNetCoupledSelfLoop :
  ∀ s → NoisyNetStep s s
noisyNetCoupledSelfLoop = noisyNetSelfLoopProof

noisyNetCoupledProjectionLift :
  (∀ x → toRepresentation (fromRepresentation x) ≡ x)
  ×
  (∀ {x y} → softsignGatedStep x y
     → NoisyNetStep (fromRepresentation x) (fromRepresentation y))
  ×
  (∀ {s t} → NoisyNetStep s t
     → softsignGatedStep (toRepresentation s) (toRepresentation t))
noisyNetCoupledProjectionLift =
  representation-project-lift
  , (λ step → representation-step-lift step)
  , (λ step → representation-step-project step)

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

-- Strict theorem extension: the full coupled theorem contains a genuine
-- hidden-state degree of freedom that is erased by the softsign-gated
-- representation projection. Hence representation reachability alone cannot
-- establish full-state communication without an additional lift theorem.
noisyNetStrictStateExtension :
  (∀ x → toRepresentation (fromRepresentation x) ≡ x)
  ×
  (toRepresentation
    (coupledNoisyNetState (gateParams zero8 zero8) zero8)
   ≡
   toRepresentation
    (coupledNoisyNetState (gateParams zero8 one8) zero8))
  ×
  (gateParams zero8 zero8 ≢ gateParams zero8 one8)
noisyNetStrictStateExtension =
  representation-project-lift
  , hiddenGateSameRepresentation
  , hiddenGateDistinct

-- The Noisy-Net theorem is therefore a coupled-state extension of the
-- representation theorem, not merely another witness bundle.
noisyNetFullCompositionTheorem :
  Irreducible NoisyNetStep
  × SelfLoop NoisyNetStep
  × Irreducible softsignGatedStep
  × SelfLoop softsignGatedStep
  × PeriodOne softsignGatedStep
  ×
    ((∀ x → toRepresentation (fromRepresentation x) ≡ x)
     ×
     (∀ {x y} → softsignGatedStep x y
        → NoisyNetStep (fromRepresentation x) (fromRepresentation y)))
noisyNetFullCompositionTheorem =
  noisyNetIrreducibilityProof
  , noisyNetSelfLoopProof
  , noisyNetRepresentationIrreducible
  , noisyNetRepresentationSelfLoop
  , noisyNetRepresentationPeriodOne
  , (representation-project-lift , (λ step → representation-step-lift step))
