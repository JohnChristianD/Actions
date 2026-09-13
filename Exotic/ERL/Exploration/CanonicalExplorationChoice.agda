{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.CanonicalExplorationChoice where

open import Data.Nat using (ℕ; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.Exploration.CanonicalMR15GA using
  ( dimension
  ; populationSize
  ; Coordinate
  ; Population
  ; Noise
  ; mutateGenome
  ; initialExponent
  )
open import Exotic.ERL.Exploration.FiniteNoise using (pos; neg; zero)

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

record DirectLatticeExplorer : Set₁ where
  field
    coordinateCount : ℕ
    positiveNoise : Coordinate → Noise → Set
    negativeNoise : Coordinate → Noise → Set
    neutralNoise : Coordinate → Noise → Set

canonicalMR15Explorer : DirectLatticeExplorer
canonicalMR15Explorer =
  record
    { coordinateCount = populationCoordinateAxes
    ; positiveNoise = λ j n →
        mutateGenome initialExponent pos j (λ _ → _)
        ≡ mutateGenome initialExponent n j (λ _ → _)
    ; negativeNoise = λ j n →
        mutateGenome initialExponent neg j (λ _ → _)
        ≡ mutateGenome initialExponent n j (λ _ → _)
    ; neutralNoise = λ j n →
        mutateGenome initialExponent zero j (λ _ → _)
        ≡ mutateGenome initialExponent n j (λ _ → _)
    }
