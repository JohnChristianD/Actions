{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.FiniteNoise where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

-- Explicit finite, non-Gaussian law: probabilities 1/4, 1/2, 1/4.
data Noise : Set where
  neg zero pos : Noise

weight : Noise → Nat
weight neg = 1
weight zero = 2
weight pos = 1

totalWeight : weight neg + weight zero + weight pos ≡ 4
totalWeight = refl

zeroHasPositiveMass : weight zero ≡ 2
zeroHasPositiveMass = refl

supportHasThreeValues : Noise → Nat
supportHasThreeValues neg = 1
supportHasThreeValues zero = 2
supportHasThreeValues pos = 3
