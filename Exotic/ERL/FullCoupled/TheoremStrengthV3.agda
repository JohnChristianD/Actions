{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.TheoremStrengthV3 where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Exotic.efficient_chad.Int8 using (Int8; zero8; one8)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; Irreducible
  ; SelfLoop
  ; PeriodOne
  ; periodOne
  ; there
  ; here
  )
open import Exotic.ERL.Exploration.MR15Reachability using
  ( MR15State
  ; MR15Step
  ; mr15IrreducibilityProof
  ; mr15SelfLoopProof
  ; openESProjection
  ; openESLift
  ; mr15-openES-retraction
  )
open import Exotic.ERL.Exploration.OpenESDyadic using
  ( OpenESState
  ; openESStep
  ; openESStepFromFreshNoise
  ; openESNoise
  ; target
  )
open import Exotic.ERL.FullCoupled.NoisyNetCoupled using
  ( CoupledNoisyNetState
  ; coupledNoisyNetState
  ; GateParams
  ; gateParams
  ; gateParameters
  ; learnerState
  ; NoisyNetStep
  )
open import Exotic.ERL.FullCoupled.SoftsignGatedRepresentation using
  ( SoftsignGatedStep
  ; softsignTarget
  ; RepresentationFactor
  ; noisyNetSoftsignFactor
  )

record TheoremFactor {S R : Set}
    (stepS : S → S → Set) (stepR : R → R → Set) : Set₁ where
  constructor theoremFactor
  field
    project : S → R
    lift : R → S
    retract : ∀ r → project (lift r) ≡ r
    projectStep : ∀ {s t} → stepS s t → stepR (project s) (project t)
    liftStep : ∀ {r q} → stepR r q → stepS (lift r) (lift q)

projectReach : ∀ {S R : Set}
    {stepS : S → S → Set} {stepR : R → R → Set}
  → TheoremFactor stepS stepR
  → ∀ {s t} → Reach stepS s t → Reach stepR (TheoremFactor.project _ s) (TheoremFactor.project _ t)
projectReach f here = here
projectReach f (there p q) = there
  (TheoremFactor.projectStep f p)
  (projectReach f q)

factorIrreducible : ∀ {S R : Set}
    {stepS : S → S → Set} {stepR : R → R → Set}
  → TheoremFactor stepS stepR
  → Irreducible stepS
  → Irreducible stepR
factorIrreducible f r s t =
  projectReach f (r (TheoremFactor.lift f s) (TheoremFactor.lift f t))

factorSelfLoop : ∀ {S R : Set}
    {stepS : S → S → Set} {stepR : R → R → Set}
  → TheoremFactor stepS stepR
  → SelfLoop stepS
  → SelfLoop stepR
factorSelfLoop f l s =
  TheoremFactor.projectStep f (l (TheoremFactor.lift f s))

factorPeriodOne : ∀ {S R : Set}
    {stepS : S → S → Set} {stepR : R → R → Set}
  → TheoremFactor stepS stepR
  → PeriodOne stepS
  → PeriodOne stepR
factorPeriodOne f (periodOne r l) =
  periodOne (factorIrreducible f r) (factorSelfLoop f l)

mr15ToOpenES : TheoremFactor MR15Step openESStep
mr15ToOpenES = theoremFactor
  openESProjection
  openESLift
  mr15-openES-retraction
  project-step
  lift-step
  where
  project-step : ∀ {s t} → MR15Step s t → openESStep (openESProjection s) (openESProjection t)
  project-step (softsignTarget q) =
    openESStepFromFreshNoise (openESNoise (proj₁ q))

  lift-step : ∀ {r q} → openESStep r q → MR15Step (openESLift r) (openESLift q)
  lift-step (openESStepFromFreshNoise ε) = softsignTarget (target ε , zero8)

noisyNetToMR15 : TheoremFactor NoisyNetStep MR15Step
noisyNetToMR15 = theoremFactor
  (RepresentationFactor.project noisyNetSoftsignFactor)
  (RepresentationFactor.lift noisyNetSoftsignFactor)
  (RepresentationFactor.retract noisyNetSoftsignFactor)
  (RepresentationFactor.projectStep noisyNetSoftsignFactor)
  (RepresentationFactor.liftStep noisyNetSoftsignFactor)

openESPeriodOneFromMR15 :
  PeriodOne MR15Step → PeriodOne openESStep
openESPeriodOneFromMR15 = factorPeriodOne mr15ToOpenES

mr15PeriodOneFromNoisyNet :
  PeriodOne NoisyNetStep → PeriodOne MR15Step
mr15PeriodOneFromNoisyNet = factorPeriodOne noisyNetToMR15

one8≢zero8 : one8 ≡ zero8 → ⊥
one8≢zero8 ()

mr15StrictWitness :
  (openESProjection (one8 , zero8) ≡ openESProjection (one8 , one8))
  × ((one8 , zero8) ≢ (one8 , one8))
mr15StrictWitness =
  refl , λ eq → one8≢zero8 (cong proj₂ eq)

noisyNetStrictWitness :
  (RepresentationFactor.project noisyNetSoftsignFactor
    (coupledNoisyNetState (gateParams zero8 zero8) zero8)
   ≡
   RepresentationFactor.project noisyNetSoftsignFactor
    (coupledNoisyNetState (gateParams zero8 one8) zero8))
  ×
  (coupledNoisyNetState (gateParams zero8 zero8) zero8
   ≢
   coupledNoisyNetState (gateParams zero8 one8) zero8)
noisyNetStrictWitness =
  refl
  , λ eq → one8≢zero8
      (cong (λ s → GateParams.sigma3 (gateParameters s)) eq)

record StrictTheoremExtension {S R : Set}
    (stepS : S → S → Set) (stepR : R → R → Set)
    (s₁ s₂ : S) : Set₁ where
  constructor strictTheoremExtension
  field
    factor : TheoremFactor stepS stepR
    sameProjection : TheoremFactor.project factor s₁ ≡ TheoremFactor.project factor s₂
    distinct : s₁ ≢ s₂

openES-lt-MR15 : StrictTheoremExtension MR15State OpenESState MR15Step openESStep
  (one8 , zero8) (one8 , one8)
openES-lt-MR15 = strictTheoremExtension mr15ToOpenES refl
  (λ eq → one8≢zero8 (cong proj₂ eq))

MR15-lt-NoisyNet : StrictTheoremExtension CoupledNoisyNetState MR15State NoisyNetStep MR15Step
  (coupledNoisyNetState (gateParams zero8 zero8) zero8)
  (coupledNoisyNetState (gateParams zero8 one8) zero8)
MR15-lt-NoisyNet = strictTheoremExtension noisyNetToMR15 refl
  (λ eq → one8≢zero8
    (cong (λ s → GateParams.sigma3 (gateParameters s)) eq))

-- Genuine strict theorem implication order:
-- OpenES < MR15 < NoisyNet.
