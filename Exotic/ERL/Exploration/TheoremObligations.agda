{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.TheoremObligations where

open import Agda.Builtin.Equality using (_≡_; refl)
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
  ; perturb
  ; mutation
  ; Reach
  )
open import Exotic.ERL.Exploration.MR15OneBit using (OneBitAperiodicityObligation)

data SelfLoop {S : Set} (step : S → S → Set) : Set where
  selfLoop : (s : S) → step s s → SelfLoop step

noisyTriStep : Int8 → Int8 → Set
noisyTriStep x y = Σ Noise (λ n → perturbScalar n x ≡ y)

noisyTriSelfLoop : SelfLoop noisyTriStep
noisyTriSelfLoop = selfLoop one8 (zero , refl)

NoisyTriAperiodicityObligation : Set
NoisyTriAperiodicityObligation =
  SelfLoop noisyTriStep × (∀ x y → ∃ (λ _ → Reach))

openESStep : Int8 → Int8 → Set
openESStep x y = Σ Noise (λ n → openESMutation n x ≡ y)

openESSelfLoop : SelfLoop openESStep
openESSelfLoop = selfLoop one8 (zero , refl)

OpenESAperiodicityObligation : Set
OpenESAperiodicityObligation =
  SelfLoop openESStep × (∀ x y → x ≡ y → Set)

mr15Step : Population → Population → Set
mr15Step p q =
  Σ StepGate (λ gate →
  Σ Exponent (λ e →
  Σ Coordinate (λ j →
  Σ Sign (λ s → mutation gate e j s p ≡ q))))

mr15SelfLoop : SelfLoop mr15Step
mr15SelfLoop = selfLoop
  (λ _ → zero8)
  (noPerturb , (Exotic.ERL.Exploration.DyadicMR15GA.unitExponent ,
    (Exotic.ERL.Exploration.DyadicMR15GA.zeroPopulation ,
      (Exotic.ERL.Exploration.DyadicMR15GA.minus ,
        Exotic.ERL.Exploration.DyadicMR15GA.noPerturbation-self-loop
          Exotic.ERL.Exploration.DyadicMR15GA.unitExponent
          (Exotic.ERL.Exploration.DyadicMR15GA.F.zero)
          Exotic.ERL.Exploration.DyadicMR15GA.minus
          (λ _ → Exotic.ERL.Exploration.DyadicMR15GA.F.zero)))))

MR15AperiodicityObligation : Set
MR15AperiodicityObligation =
  SelfLoop mr15Step × (∀ p q → Reach p q)

MR15OneBitAperiodicityObligation : Set
MR15OneBitAperiodicityObligation = OneBitAperiodicityObligation

-- These candidates are obligations only. No numeric ranking is assigned.
