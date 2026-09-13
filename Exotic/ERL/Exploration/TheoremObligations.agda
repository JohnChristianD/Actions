{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.TheoremObligations where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin)
open import Data.Product using (Σ; _×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; one8)
open import Exotic.ERL.Exploration.FiniteNoise using
  ( Noise; zero; zeroHasPositiveMass; totalWeight )
open import Exotic.ERL.Exploration.NoisyNetFinite using (perturbScalar)
open import Exotic.ERL.Exploration.DyadicOpenES using (openESMutation)
open import Exotic.ERL.Exploration.DyadicMR15GA using
  ( Population
  ; Coordinate
  ; StepGate
  ; noPerturb
  ; perturb
  ; mutation
  ; zeroPopulation
  ; canonicalZero-self-loop
  ; noPerturbation-self-loop
  )
open import Exotic.ERL.Exploration.MR15OneBit using (OneBitAperiodicityObligation)

data Reach {S : Set} (step : S → S → Set) : S → S → Set where
  here : ∀ {x} → Reach step x x
  there : ∀ {x y z} → step x y → Reach step y z → Reach step x z

SelfLoop : {S : Set} → (S → S → Set) → Set
SelfLoop {S} step = Σ S (λ s → step s s)

canonicalNoiseStep : Int8 → Int8 → Set
canonicalNoiseStep x y = Σ Noise (λ n → perturbScalar n x ≡ y)

canonicalNoiseSelfLoop : SelfLoop canonicalNoiseStep
canonicalNoiseSelfLoop = one8 , (zero , refl)

CanonicalNoiseAperiodicityObligation : Set
CanonicalNoiseAperiodicityObligation =
  SelfLoop canonicalNoiseStep × (∀ x y → Reach canonicalNoiseStep x y)

openESStep : Int8 → Int8 → Set
openESStep x y = Σ Noise (λ n → openESMutation n x ≡ y)

openESSelfLoop : SelfLoop openESStep
openESSelfLoop = one8 , (zero , refl)

OpenESAperiodicityObligation : Set
OpenESAperiodicityObligation =
  SelfLoop openESStep × (∀ x y → Reach openESStep x y)

mr15Step : Population → Population → Set
mr15Step p q =
  Σ StepGate (λ gate →
  Σ Noise (λ n →
  Σ Coordinate (λ j → mutation gate n j p ≡ q)))

mr15SelfLoop : SelfLoop mr15Step
mr15SelfLoop =
  zeroPopulation ,
  (noPerturb ,
    (zero ,
      (F.zero ,
        noPerturbation-self-loop zero F.zero zeroPopulation)))

mr15PerturbZeroSelfLoop : ∀ (p : Population) (j : Coordinate) →
  mutation perturb zero j p ≡ p
mr15PerturbZeroSelfLoop p j = canonicalZero-self-loop j p

MR15MutationReachabilityObligation : Set
MR15MutationReachabilityObligation = ∀ p q → Reach mr15Step p q

MR15AperiodicityObligation : Set
MR15AperiodicityObligation =
  SelfLoop mr15Step × MR15MutationReachabilityObligation

CanonicalDistributionArithmetic : Set
CanonicalDistributionArithmetic =
  (sumWeightWitness : totalWeight) ×
  (sumZeroWitness : zeroHasPositiveMass)
  where
  sumWeightWitness : Set
  sumWeightWitness = totalWeight
  sumZeroWitness : Set
  sumZeroWitness = zeroHasPositiveMass

MR15OneBitAperiodicityObligation : Set
MR15OneBitAperiodicityObligation = OneBitAperiodicityObligation

-- Generation-chain irreducibility is deliberately not identified with mutation reachability.
-- A complete generation theorem requires the actual selection, averaging, adaptation,
-- inner-state, and tape-state transition relation.
GenerationIrreducibilityObligation : Set
GenerationIrreducibilityObligation = Set
