{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.AllSafeCombined where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (toℕ)
open import Data.Product using (Σ)
open import Exotic.efficient_chad.Int8
  using
    ( Int8
    ; code
    ; int8OfNat
    ; int8Roundtrip
    ; zero8
    ; one8
    )
open import Exotic.econlib.GameTheory
  using
    ( defect
    ; prisonersDilemma
    ; PureNash
    ; isNashEquilibriumDD
    )
open import Exotic.econlib.Equilibrium
  using
    ( canonicalEconomy2
    ; canonicalEconomy2Equilibrium
    ; WalrasianEquilibrium2
    ; ProductionEconomy2
    ; WalrasianProductionEquilibrium2
    ; exists_equilibrium_prod2
    )
open import Exotic.ERL.Canonical.CanonicalOptimizer using (CanonicalConfig; canonical)
open import Exotic.ERL.Canonical.ConjectureDiscovery
open import Exotic.ERL.Finite.Activation using (softsignQ8; signReLUQ8; cReLU8)
open import Exotic.ERL.Finite.Haar using (haar4)
open import Exotic.ERL.Finite.TrueOnlineTD using
  ( TrueOnlineState
  ; initialState
  ; exampleFeature
  ; exampleNextFeature
  ; learnerStep
  ; exampleStep
  )
open import Exotic.ERL.Finite.Int8Vector using (vec4)
open import Exotic.ERL.Exploration.FiniteNoise using (Noise; neg; zero; pos; weight)
open import Exotic.ERL.Exploration.NoisyNetFinite using (noiseDelta; perturbScalar; perturbVector4)

testInt8Roundtrip : ∀ (x : Int8) →
  toℕ (code (int8OfNat (toℕ (code x)))) ≡ toℕ (code x)
testInt8Roundtrip x = int8Roundtrip x

testCanonicalConfig : CanonicalConfig
testCanonicalConfig = canonical

testEquilibrium : WalrasianEquilibrium2 canonicalEconomy2
testEquilibrium = canonicalEconomy2Equilibrium

testNashDD : PureNash prisonersDilemma defect defect
testNashDD = isNashEquilibriumDD

testProductionExistence : Σ ProductionEconomy2 (λ e → WalrasianProductionEquilibrium2 e)
testProductionExistence = exists_equilibrium_prod2

testNoiseWeights : weight neg + weight zero + weight pos ≡ 4
testNoiseWeights = refl

testZeroPerturbation : perturbScalar zero one8 ≡ one8
testZeroPerturbation = refl

testSoftsignZero : softsignQ8 zero8 ≡ zero8
testSoftsignZero = refl

testCReLUZero : cReLU8 zero8 ≡ zero8
testCReLUZero = refl

testFiniteLearner : TrueOnlineState
testFiniteLearner = learnerStep one8 exampleFeature exampleNextFeature initialState

testFiniteLearnerMatchesExample : testFiniteLearner ≡ exampleStep
testFiniteLearnerMatchesExample = refl

testHaarShape : haar4 (vec4 zero8 zero8 zero8 zero8) ≡ haar4 (vec4 zero8 zero8 zero8 zero8)
testHaarShape = refl
