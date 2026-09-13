{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearnerEA where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin; toℕ)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8OfNat
  ; zero8
  )
open import Exotic.ERL.Exploration.FiniteNoise using
  ( Noise
  ; zero
  )
open import Exotic.ERL.Exploration.DyadicMR15GA using
  ( StepGate
  ; noPerturb
  )
open import Exotic.ERL.Exploration.CanonicalMR15GA using
  ( Coordinate
  ; MR15State
  ; initialMR15
  ; Genome
  ; generationStep
  ; mean
  )
open import Exotic.ERL.FullCoupled.CanonicalToken using (Token; token)
open import Exotic.ERL.FullCoupled.CanonicalLearner using
  ( LearnerState
  ; start
  ; step
  ; criticValue
  )
open import Exotic.ERL.FullCoupled.FiniteAperiodicity using
  ( Path
  ; ExactReach
  ; SelfLoop
  ; Irreducible
  ; AperiodicViaConsecutiveReturns
  ; hubAperiodicity
  )

NoiseTape : Set
NoiseTape = Fin 16 → Noise

CoordinateTape : Set
CoordinateTape = Fin 16 → Coordinate

rewardZero : Int8
rewardZero = zero8

genomeToken : Genome → Token
genomeToken g =
  token
    (int8OfNat (toℕ (g F.zero)))
    (int8OfNat (toℕ (g (F.suc F.zero))))
    (int8OfNat (toℕ (g (F.suc (F.suc F.zero)))))
    (int8OfNat (toℕ (g (F.suc (F.suc (F.suc F.zero))))))

learnerFitness : LearnerState → Genome → ℕ
learnerFitness s g =
  toℕ
    (code
      (criticValue
        s
        zero
        (genomeToken g)))

record CoupledState : Set where
  constructor coupled
  field
    learner : LearnerState
    ea : MR15State

open CoupledState public

coupledStep : CoupledState →
  StepGate →
  Noise → Noise →
  NoiseTape → CoordinateTape →
  Int8 →
  CoupledState
coupledStep s gate epsilon nextEpsilon noises coords reward =
  let
    ea' = generationStep
      (learnerFitness (learner s))
      gate
      (ea s)
      noises
      coords
    meanToken = genomeToken (mean ea')
    learner' = step
      (learner s)
      epsilon
      nextEpsilon
      meanToken
      meanToken
      reward
  in coupled learner' ea'

data CoupledEdge : CoupledState → CoupledState → Set where
  edge : ∀ {s}
    (gate : StepGate)
    (epsilon nextEpsilon : Noise)
    (noises : NoiseTape)
    (coords : CoordinateTape)
    (reward : Int8) →
    CoupledEdge s
      (coupledStep
        s gate epsilon nextEpsilon noises coords reward)

data CoupledReach : CoupledState → CoupledState → Set where
  here : ∀ {s} → CoupledReach s s
  there : ∀ {s t u} →
    CoupledEdge s t →
    CoupledReach t u →
    CoupledReach s u

record CoupledIrreducibilityWitness : Set₁ where
  field
    reachable : ∀ (s t : CoupledState) → CoupledReach s t

startCoupled : CoupledState
startCoupled = coupled start initialMR15

zeroNoiseTape : NoiseTape
zeroNoiseTape _ = zero

zeroCoordinateTape : CoordinateTape
zeroCoordinateTape _ = F.zero

startCoupledSelfLoop : CoupledEdge startCoupled startCoupled
startCoupledSelfLoop =
  edge
    noPerturb
    zero
    zero
    zeroNoiseTape
    zeroCoordinateTape
    zero8

record CoupledSelfLoop : Set where
  constructor coupledSelfLoop
  field
    at : CoupledState
    holds : CoupledEdge at at

startSelfLoop : CoupledSelfLoop
startSelfLoop = coupledSelfLoop startCoupled startCoupledSelfLoop

exactReach : ∀ {s t : CoupledState} →
  CoupledReach s t → ExactReach CoupledEdge s t
exactReach here = 0 , []ᵖ
exactReach (there e r) =
  exactTrans (1 , e ∷ᵖ []ᵖ) (exactReach r)

record CoupledAperiodicityWitness : Set₁ where
  field
    witness : AperiodicViaConsecutiveReturns CoupledEdge

CoupledIrreducibility : Set
CoupledIrreducibility = ∀ (s t : CoupledState) → CoupledReach s t

coupledIrreducibility :
  CoupledIrreducibility →
  Irreducible CoupledEdge
coupledIrreducibility reach =
  record
    { reach = λ s t → exactReach (reach s t)
    }

coupledAperiodicity :
  CoupledIrreducibility →
  CoupledAperiodicityWitness
coupledAperiodicity reach =
  record
    { witness =
        hubAperiodicity
          (coupledIrreducibility reach)
          (record
            { hub = CoupledSelfLoop.at startSelfLoop
            ; loop = CoupledSelfLoop.holds startSelfLoop
            })
    }
