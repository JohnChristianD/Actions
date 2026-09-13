{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.DyadicOpenES where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8; int8Add; one8)
open import Exotic.ERL.Exploration.FiniteNoise using (Noise; noiseCode; zero)

openESMutation : Noise → Int8 → Int8
openESMutation n x = int8Add x (noiseCode n)

openESZeroSelfLoop : openESMutation zero one8 ≡ one8
openESZeroSelfLoop = refl

openESHasPositiveNeutralMass : ∀ {x : Int8} → openESMutation zero x ≡ x
openESHasPositiveNeutralMass {x} = refl
