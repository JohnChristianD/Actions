{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.CanonicalExplorationChoice where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin; fromℕ<; toℕ)
open import Data.Nat using (ℕ; _*_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; int8Mul)
open import Exotic.ERL.Exploration.FiniteNoise using (Noise)
open import Exotic.ERL.Exploration.CanonicalMR15GA using
  ( dimension
  ; populationSize
  ; Coordinate
  ; Genome
  ; Population
  ; V
  ; Exponent
  ; lookupV
  ; mutateGenome
  ; mutatePopulation
  ; StepGate
  ; perturb
  )
open import Exotic.ERL.FullCoupled.CanonicalTransformer using
  ( Pair
  ; pair
  ; GateParameters
  ; gate
  ; gateWeight
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

gateDiagonal :
  ∀ (gp : GateParameters) (epsilon : Noise) (x : Int8) →
  gate gp epsilon (pair x x) ≡
  pair
    (int8Mul (gateWeight gp epsilon) x)
    (int8Mul (gateWeight gp epsilon) x)
gateDiagonal gp epsilon x = refl

mutatePopulationCoordinate :
  ∀ (e : Exponent)
  (base : Population)
  (noises : Fin 16 → Noise)
  (coords : Fin 16 → Coordinate)
  (elites : V Genome 4)
  (i : Fin 16) →
  mutatePopulation perturb e base noises coords elites i ≡
    mutateGenomeAt i
  where
  mutateGenomeAt : Fin 16 → Genome
  mutateGenomeAt i =
    let
      j = coords i
      k = fromℕ< (m%n<n (toℕ i) 4)
    in lookupGenome e (noises i) j k

  lookupGenome : Exponent → Noise → Coordinate → Fin 4 → Genome
  lookupGenome e n j k =
    mutateGenome e n j (lookupV k elites)

mutatePopulationCoordinate e base noises coords elites i = refl
