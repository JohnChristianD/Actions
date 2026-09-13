{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.CanonicalExplorationChoice where

open import Data.Nat using (ℕ; _<_ ; _*_; suc)
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

mr15HasMoreDirectExplorationAxes :
  noisyNetDirectNoiseAxes < populationCoordinateAxes
mr15HasMoreDirectExplorationAxes = refl

canonicalExplorationCriterion :
  populationCoordinateAxes ≡ 64 ×
  noisyNetDirectNoiseAxes ≡ 1 ×
  noisyNetDirectNoiseAxes < populationCoordinateAxes
canonicalExplorationCriterion =
  refl , refl , refl
