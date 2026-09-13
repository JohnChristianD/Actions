{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.CanonicalExplorationChoice where

open import Data.Nat using (ℕ; _*_)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.Exploration.CanonicalMR15GA using
  ( dimension
  ; populationSize
  )

populationCoordinateAxes : ℕ
populationCoordinateAxes = populationSize * dimension

populationCoordinateAxesWitness :
populationCoordinateAxes ≡ 64
populationCoordinateAxesWitness = refl

noisyNetDirectNoiseAxes : ℕ
noisyNetDirectNoiseAxes = 1

noisyNetDirectNoiseAxesWitness :
  noisyNetDirectNoiseAxes ≡ 1
noisyNetDirectNoiseAxesWitness = refl

canonicalExplorationCriterion :
  populationCoordinateAxes ≡ 64 ×
  noisyNetDirectNoiseAxes ≡ 1
canonicalExplorationCriterion =
  refl , refl
