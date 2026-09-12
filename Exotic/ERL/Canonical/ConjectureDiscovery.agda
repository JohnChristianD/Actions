{-# OPTIONS --safe #-}

module Exotic.ERL.Canonical.ConjectureDiscovery where

open import Agda.Builtin.Equality using (_≡_; refl)
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
open import Exotic.ERL.Finite.TrueOnlineTD using (TrueOnlineState; exampleStep; initialState)
open import Exotic.ERL.Exploration.FiniteNoise using (weight; neg; zero; pos; totalWeight)
open import Exotic.ERL.Exploration.FiniteMarkov using (transition; selfLoopExample; selfLoopWeight)
open import Exotic.ERL.Exploration.ComposedLearnerExploration using (zeroStep; zeroStep-is-initial)
open import Exotic.ERL.Exploration.FullLearnerNoisyTri using (Parameters; Window2; zeroNoisePreservesLearner)
open import Exotic.ERL.Representation.Haar2 using (HaarPair; haarPair; haar2-square-scale)

data SurvivingConjecture : Set where
  int8Roundtrip : SurvivingConjecture
  prisonersDilemmaDD : SurvivingConjecture
  canonicalEquilibrium : SurvivingConjecture
  productionExistence : SurvivingConjecture
  finiteNoiseNormalises : SurvivingConjecture
  concreteZeroNoiseSelfLoop : SurvivingConjecture
  concreteZeroNoiseWeight : SurvivingConjecture
  composedZeroSelfLoop : SurvivingConjecture
  quantizedSoftsignZero : SurvivingConjecture
  quantizedCReluZero : SurvivingConjecture
  learnerExampleExists : SurvivingConjecture
  fullNoisyTriZeroPreserves : SurvivingConjecture
  haar2SquareScale : SurvivingConjecture

proof : ∀ c → Set
proof int8Roundtrip = ∀ (x : Int8) →
  toℕ (code (int8OfNat (toℕ (code x)))) ≡ toℕ (code x)
proof prisonersDilemmaDD = PureNash prisonersDilemma defect defect
proof canonicalEquilibrium = WalrasianEquilibrium2 canonicalEconomy2
proof productionExistence = Σ ProductionEconomy2 (λ e → WalrasianProductionEquilibrium2 e)
proof finiteNoiseNormalises = weight neg + weight zero + weight pos ≡ 4
proof concreteZeroNoiseSelfLoop = transition zero one8 ≡ one8
proof concreteZeroNoiseWeight = weight zero ≡ 2
proof composedZeroSelfLoop = zeroStep ≡ initialState
proof quantizedSoftsignZero = softsignQ8 zero8 ≡ zero8
proof quantizedCReluZero = cReLU8 zero8 ≡ zero8
proof learnerExampleExists = TrueOnlineState
proof fullNoisyTriZeroPreserves = ∀ (p : Parameters) (w : Window2) →
  zeroNoisePreservesLearner p w
proof haar2SquareScale = ∀ x y →
  haar2 (haar2 (haarPair x y)) ≡ haarPair (x + x) (y + y)

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

survivesSelfLoop : proof concreteZeroNoiseSelfLoop
survivesSelfLoop = selfLoopExample

survivesSelfLoopWeight : proof concreteZeroNoiseWeight
survivesSelfLoopWeight = selfLoopWeight

survivesComposedSelfLoop : proof composedZeroSelfLoop
survivesComposedSelfLoop = zeroStep-is-initial

survivesSoftsignZero : proof quantizedSoftsignZero
survivesSoftsignZero = refl

survivesCReLUZero : proof quantizedCReluZero
survivesCReLUZero = refl

survivesLearnerExample : proof learnerExampleExists
survivesLearnerExample = exampleStep

survivesFullNoisyTriZero : proof fullNoisyTriZeroPreserves
survivesFullNoisyTriZero p w = zeroNoisePreservesLearner p w

survivesHaar2SquareScale : proof haar2SquareScale
survivesHaar2SquareScale = haar2-square-scale
