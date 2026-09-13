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
  ( MR15Index
  ; Population
  ; Mutation
  ; emptyPopulation
  ; mutate
  )

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
  Σ Mutation (λ m → Σ MR15Index (λ i → mutate m i p ≡ q))

mr15SelfLoop : SelfLoop mr15Step
mr15SelfLoop = emptyPopulation , (neutral , (F.zero , refl))

MR15AperiodicityObligation : Set
MR15AperiodicityObligation =
  SelfLoop mr15Step × (∀ p q → Reach mr15Step p q)

-- The three candidates above are obligations only.
-- No numeric ranking is assigned until the corresponding theorem is proved.
