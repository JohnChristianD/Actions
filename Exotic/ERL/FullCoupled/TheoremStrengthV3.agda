{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.TheoremStrengthV3 where

open import Agda.Builtin.Equality using (_≡_; refl; cong; trans)
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
  )
open import Exotic.ERL.FullCoupled.NoisyNetSoftsignFactor using
  ( RepresentationFactor
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

composeFactor : ∀ {S R T : Set}
    {stepS : S → S → Set} {stepR : R → R → Set} {stepT : T → T → Set}
  → TheoremFactor stepS stepR
  → TheoremFactor stepR stepT
  → TheoremFactor stepS stepT
composeFactor f g = theoremFactor
  (λ s → TheoremFactor.project g (TheoremFactor.project f s))
  (λ t → TheoremFactor.lift f (TheoremFactor.lift g t))
  retract
  project-step
  lift-step
  where
  retract : ∀ t →
    TheoremFactor.project g
      (TheoremFactor.project f
        (TheoremFactor.lift f (TheoremFactor.lift g t))) ≡ t
  retract t =
    trans
      (cong (TheoremFactor.project g)
        (TheoremFactor.retract f (TheoremFactor.lift g t)))
      (TheoremFactor.retract g t)

  project-step : ∀ {s t}
    → stepS s t
    → stepT
        (TheoremFactor.project g (TheoremFactor.project f s))
        (TheoremFactor.project g (TheoremFactor.project f t))
  project-step p =
    TheoremFactor.projectStep g (TheoremFactor.projectStep f p)

  lift-step : ∀ {r q}
    → stepT r q
    → stepS
        (TheoremFactor.lift f (TheoremFactor.lift g r))
        (TheoremFactor.lift f (TheoremFactor.lift g q))
  lift-step p =
    TheoremFactor.liftStep f (TheoremFactor.liftStep g p)

record StrictFactorExtension {S R : Set}
    (stepS : S → S → Set) (stepR : R → R → Set) : Set₁ where
  constructor strictFactorExtension
  field
    factor : TheoremFactor stepS stepR
    witness₁ witness₂ : S
    sameProjection :
      TheoremFactor.project factor witness₁
      ≡
      TheoremFactor.project factor witness₂
    distinct : witness₁ ≢ witness₂

composeStrictFactor : ∀ {S R T : Set}
    {stepS : S → S → Set} {stepR : R → R → Set} {stepT : T → T → Set}
  → StrictFactorExtension stepS stepR
  → TheoremFactor stepR stepT
  → StrictFactorExtension stepS stepT
composeStrictFactor strict g =
  strictFactorExtension
    (composeFactor (StrictFactorExtension.factor strict) g)
    (StrictFactorExtension.witness₁ strict)
    (StrictFactorExtension.witness₂ strict)
    (cong (TheoremFactor.project g)
      (StrictFactorExtension.sameProjection strict))
    (StrictFactorExtension.distinct strict)

projectReach : ∀ {S R : Set}
    {stepS : S → S → Set} {stepR : R → R → Set}
  → TheoremFactor stepS stepR
  → ∀ {s t} → Reach stepS s t
  → Reach stepR (TheoremFactor.project _ s) (TheoremFactor.project _ t)
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

noisyNetToOpenES : TheoremFactor NoisyNetStep openESStep
noisyNetToOpenES = composeFactor noisyNetToMR15 mr15ToOpenES

openESPeriodOneFromMR15 :
  PeriodOne MR15Step → PeriodOne openESStep
openESPeriodOneFromMR15 = factorPeriodOne mr15ToOpenES

mr15PeriodOneFromNoisyNet :
  PeriodOne NoisyNetStep → PeriodOne MR15Step
mr15PeriodOneFromNoisyNet = factorPeriodOne noisyNetToMR15

one8≢zero8 : one8 ≡ zero8 → ⊥
one8≢zero8 ()

mr15Strict :
  StrictFactorExtension MR15Step openESStep
mr15Strict = strictFactorExtension mr15ToOpenES
  (one8 , zero8)
  (one8 , one8)
  refl
  (λ eq → one8≢zero8 (cong proj₂ eq))

noisyNetStrict :
  StrictFactorExtension NoisyNetStep MR15Step
noisyNetStrict = strictFactorExtension noisyNetToMR15
  (coupledNoisyNetState (gateParams zero8 zero8) zero8)
  (coupledNoisyNetState (gateParams zero8 one8) zero8)
  refl
  (λ eq → one8≢zero8
    (cong (λ s → GateParams.sigma3 (gateParameters s)) eq))

noisyNetStrictOverOpenES :
  StrictFactorExtension NoisyNetStep openESStep
noisyNetStrictOverOpenES = composeStrictFactor noisyNetStrict mr15ToOpenES

openES-lt-MR15 : StrictFactorExtension MR15Step openESStep
openES-lt-MR15 = mr15Strict

MR15-lt-NoisyNet : StrictFactorExtension NoisyNetStep MR15Step
MR15-lt-NoisyNet = noisyNetStrict

openES-lt-NoisyNet : StrictFactorExtension NoisyNetStep openESStep
openES-lt-NoisyNet = noisyNetStrictOverOpenES

-- The strict ordering is now a transitive semantic factor theorem:
-- OpenES < MR15 < NoisyNet, with the composite NoisyNet→OpenES factor
-- and its inherited proper fiber explicitly constructed in Agda.
