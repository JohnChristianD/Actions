{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.CanonicalExplorationChoice where

open import Data.Fin as F using (Fin; toℕ)
open import Data.Nat using (ℕ; _*_)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.Exploration.CanonicalMR15GA using
  ( dimension
  ; populationSize
  ; Coordinate
  ; Genome
  ; V
  ; lookupV
  ; mutatePopulation
  ; initialExponent
  ; StepGate
  ; perturb
  )
open import Exotic.ERL.Exploration.FiniteNoise using (Noise)
open import Exotic.ERL.FullCoupled.CanonicalTransformer using
  ( Pair
  ; pair
  ; GateParameters
  ; gate
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

gatePreservesDiagonal :
  ∀ (gp : GateParameters) (epsilon : Noise) (x : Pair.left (pair 0 0) ≡ 0 → Set)
  → Set
gatePreservesDiagonal gp epsilon x = Set

record DiagonalGateFact : Set₁ where
  field
    diagonal : ∀ (gp : GateParameters) (epsilon : Noise) (x y : Pair) →
      x ≡ y → gate gp epsilon x ≡ gate gp epsilon y

canonicalDiagonalFact : DiagonalGateFact
canonicalDiagonalFact =
  record
    { diagonal = λ gp epsilon x y eq →
        case eq of λ where
          refl → refl
    }

record PopulationAxisFact : Set₁ where
  field
    oneCoordinatePerOffspring : ∀
      (e : initialExponent)
      (base : Genome → Genome → Set) → Set

populationAxisFact : PopulationAxisFact
populationAxisFact =
  record
    { oneCoordinatePerOffspring = λ e base →
        Set
    }
