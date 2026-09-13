{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.TheoremObligations where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin)
open import Data.Product using (Σ; _×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; one8)
open import Exotic.ERL.Exploration.FiniteNoise using (Noise; zero)
open import Exotic.ERL.Exploration.NoisyNetFinite using (perturbScalar)
open import Exotic.ERL.Exploration.DyadicOpenES using (openESMutation)
open import Exotic.ERL.Exploration.DyadicMR15GA using
  ( Population
  ; Coordinate
  ; Exponent
  ; Sign
  ; StepGate
  ; noPerturb
  ; mutation
  ; zeroPopulation
  ; unitExponent
  ; minus
  ; noPerturbation-self-loop
  )
open import Exotic.ERL.Exploration.MR15OneBit using (OneBitAperiodicityObligation)

data Reach {S : Set} (step : S → S → Set) : S → S → Set where
  here : ∀ {x} → Reach step x x
  there : ∀ {x y z} → step x y → Reach step y z → Reach step x z

SelfLoop : {S : Set} → (S → S → Set) → Set
SelfLoop {S} step = Σ S (λ s → step s s)

noisyTriStep : Int8 → Int8 → Set
noisyTriStep x y = Σ Noise (λ n → perturbScalar n x ≡ y)

noisyTriSelfLoop : SelfLoop noisyTriStep
noisyTriSelfLoop = one8 , (zero , refl)

NoisyTriAperiodicityObligation : Set
NoisyTriAperiodicityObligation =
  SelfLoop noisyTriStep × (∀ x y → Reach noisyTriStep x y)

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
  Σ Exponent (λ e →
  Σ Coordinate (λ j →
  Σ Sign (λ s → mutation gate e j s p ≡ q))))

mr15SelfLoop : SelfLoop mr15Step
mr15SelfLoop =
  zeroPopulation ,
  (noPerturb ,
    (unitExponent ,
      (F.zero ,
        (minus ,
          noPerturbation-self-loop unitExponent F.zero minus zeroPopulation))))

MR15AperiodicityObligation : Set
MR15AperiodicityObligation =
  SelfLoop mr15Step × (∀ p q → Reach mr15Step p q)

MR15OneBitAperiodicityObligation : Set
MR15OneBitAperiodicityObligation = OneBitAperiodicityObligation

-- No numeric ranking is assigned.  These are independent kernel obligations.
