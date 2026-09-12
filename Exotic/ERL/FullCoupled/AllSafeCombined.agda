{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.AllSafeCombined where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin; toℕ)
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
open import Exotic.ERL.Finite.Activation using (softsignQ8; cReLU8)
open import Exotic.ERL.Finite.TrueOnlineTD using
  ( TrueOnlineState
  ; initialState
  ; exampleFeature
  ; exampleNextFeature
  ; learnerStep
  )
open import Exotic.ERL.Exploration.FiniteNoise using (neg; zero; pos; weight)
open import Exotic.ERL.Exploration.NoisyNetFinite using (perturbScalar)
open import Exotic.ERL.Exploration.FiniteMarkov using (selfLoopExample)
open import Exotic.ERL.Exploration.ComposedLearnerExploration using
  ( composedExploreStep
  ; zeroStep
  ; zeroStep-is-initial
  )
open import Exotic.ERL.Exploration.DyadicMR15GA using
  ( Mutation
  ; mutate
  ; population-nonempty
  ; mr15NeutralCertificate
  ; mr15MutationWitness
  )
open import Exotic.ERL.Exploration.DMCPFinite using
  ( DMCPState
  ; finite-dmcp-nonempty
  ; neutral-preserves
  )
open import Exotic.ERL.Exploration.TheoremRanking using
  ( Rank
  ; canonicalTheoremClass
  ; mr15DyadicRank
  ; mr15DominanceOnFiniteCriteria
  )
open import Exotic.ERL.Representation.HaarInt8 using
  ( H8
  ; double8
  ; H8-square
  )
open import Exotic.ERL.FullCoupled.FiniteLearningCertificate using
  ( LearnState
  ; prediction
  ; trainingWitness
  ; trainedWitness
  ; trainingWitness-learns
  ; trainingWitness-nonempty
  ; trainingWitness-target
  )
open import Exotic.ERL.FullCoupled.FiniteLearner using
  ( Parameters
  ; parameters
  ; Token
  ; token
  ; Window2
  ; window2
  ; learnForward
  )

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
testZeroPerturbation = selfLoopExample

testSoftsignZero : softsignQ8 zero8 ≡ zero8
testSoftsignZero = refl

testCReLUZero : cReLU8 zero8 ≡ zero8
testCReLUZero = refl

testFiniteLearner : TrueOnlineState
testFiniteLearner = learnerStep one8 exampleFeature exampleNextFeature initialState

testComposedExploration : TrueOnlineState
testComposedExploration = composedExploreStep zero zero8 exampleFeature exampleNextFeature initialState

sampleParameters : Parameters
sampleParameters = parameters one8 one8 one8 one8 one8 one8

sampleToken : Token
sampleToken = token one8 zero8 zero8 one8

sampleWindow : Window2
sampleWindow = window2 sampleToken sampleToken

testFullForward : Int8
testFullForward = learnForward sampleParameters sampleWindow

testComposedExplorationStable : composedExploreStep zero zero8 exampleFeature exampleNextFeature initialState ≡ initialState
testComposedExplorationStable = zeroStep-is-initial

testHaarSquare : ∀ (x y : Int8) → H8 (H8 (x , y)) ≡ (double8 x , double8 y)
testHaarSquare = H8-square

testMR15Nonempty : Mutation
testMR15Nonempty = neutral

testMR15Neutral : mutate neutral F.zero population-nonempty ≡ population-nonempty
testMR15Neutral = mr15NeutralCertificate

testMR15Mutation : mr15MutationWitness
testMR15Mutation = mr15MutationWitness

testDMCPNonempty : DMCPState
testDMCPNonempty = finite-dmcp-nonempty

testDMCPNeutral : ∀ (s : DMCPState) → neutral-preserves s
testDMCPNeutral = neutral-preserves

testMR15Ranking : Rank
testMR15Ranking = mr15DyadicRank

testMR15RankingArithmetic : mr15DominanceOnFiniteCriteria
testMR15RankingArithmetic = mr15DominanceOnFiniteCriteria

testCanonicalRanking : Rank
testCanonicalRanking = canonicalTheoremClass

testLearningState : LearnState
testLearningState = trainedWitness

testLearningNonempty : prediction trainingWitness ≡ zero8
testLearningNonempty = trainingWitness-nonempty

testLearningExact : prediction trainedWitness ≡ int8OfNat 4
testLearningExact = trainingWitness-learns

testLearningTargetValue : LearnState.target trainingWitness ≡ int8OfNat 4
testLearningTargetValue = trainingWitness-target
