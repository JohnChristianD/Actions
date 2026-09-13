{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.DyadicOpenES where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8; int8Add; one8; zero8)
open import Exotic.ERL.Exploration.FiniteNoise using (Noise; neg; zero; pos)

openESMutation : Noise → Int8 → Int8
openESMutation neg x = int8Add x (int8Add one8 one8)
openESMutation zero x = x
openESMutation pos x = int8Add x one8

openESZeroSelfLoop : openESMutation zero one8 ≡ one8
openESZeroSelfLoop = refl

openESHasPositiveNeutralMass : ∀ {x : Int8} → openESMutation zero x ≡ x
openESHasPositiveNeutralMass = refl
