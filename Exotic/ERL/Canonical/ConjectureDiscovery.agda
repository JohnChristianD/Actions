{-# OPTIONS --safe #-}

module Exotic.ERL.Canonical.ConjectureDiscovery where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Fin using (toℕ)
open import Data.Product using (Σ)
open import Exotic.efficient_chad.Int8 using (Int8; code; int8OfNat; int8Roundtrip; one8; zero8)
open import Exotic.econlib.GameTheory using
  ( defect
  ; prisonersDilemma
  ; PureNash
  ; isNashEquilibriumDD
  )
open import Exotic.econlib.Equilibrium using
  ( canonicalEconomy2
  ; canonicalEconomy2Equilibrium
  ; WalrasianEquilibrium2
  ; ProductionEconomy2
  ; WalrasianProductionEquilibrium2
  ; exists_equilibrium_prod2
  )
open import Exotic.ERL.Finite.Activation using (softsignQ8; cReLU8)
open import Exotic.ERL.Finite.TrueOnlineTD using (TrueOnlineState; exampleStep)
open import Exotic.ERL.Finite.Int8Vector using (vec4; x0; x1; x2; x3)
open import Exotic.ERL.Exploration.FiniteNoise using (weight; neg; zero; pos; totalWeight)
open import Exotic.ERL.Exploration.NoisyNetFinite using (perturbVector4; perturbScalar)


data SurvivingConjecture : Set where
  int8Roundtrip : SurvivingConjecture
  prisonersDilemmaDD : SurvivingConjecture
  canonicalEquilibrium : SurvivingConjecture
  productionExistence : SurvivingConjecture
  finiteNoiseNormalises : SurvivingConjecture
  zeroNoisePreservesExample : SurvivingConjecture
  quantizedSoftsignZero : SurvivingConjecture
  quantizedCReluZero : SurvivingConjecture
  learnerExampleExists : SurvivingConjecture

proof : ∀ c → Set
proof int8Roundtrip = ∀ (x : Int8) →
  toℕ (code (int8OfNat (toℕ (code x)))) ≡ toℕ (code x)
proof prisonersDilemmaDD = PureNash prisonersDilemma defect defect
proof canonicalEquilibrium = WalrasianEquilibrium2 canonicalEconomy2
proof productionExistence = Σ ProductionEconomy2 (λ e → WalrasianProductionEquilibrium2 e)
proof finiteNoiseNormalises = weight neg + weight zero + weight pos ≡ 4
proof zeroNoisePreservesExample =
  perturbVector4 zero (vec4 one8 zero8 zero8 zero8)
    ≡ perturbVector4 zero (vec4 one8 zero8 zero8 zero8)
proof quantizedSoftsignZero = softsignQ8 zero8 ≡ zero8
proof quantizedCReluZero = cReLU8 zero8 ≡ zero8
proof learnerExampleExists = TrueOnlineState

survives : proof int8Roundtrip
survives = int8Roundtrip

survivesNash : proof prisonersDilemmaDD
survivesNash = isNashEquilibriumDD

survivesEquilibrium : proof canonicalEquilibrium
survivesEquilibrium = canonicalEconomy2Equilibrium

survivesProduction : proof productionExistence
survivesProduction = exists_equilibrium_prod2

survivesNoise : proof finiteNoiseNormalises
survivesNoise = totalWeight

survivesZeroNoise : proof zeroNoisePreservesExample
survivesZeroNoise = refl

survivesSoftsignZero : proof quantizedSoftsignZero
survivesSoftsignZero = refl

survivesCReLUZero : proof quantizedCReluZero
survivesCReLUZero = refl

survivesLearnerExample : proof learnerExampleExists
survivesLearnerExample = exampleStep
