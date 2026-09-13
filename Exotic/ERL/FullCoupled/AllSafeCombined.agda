{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.AllSafeCombined where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin; toℕ)
open import Data.Product using (Σ)
open import Exotic.efficient_chad.Int8 using
  ( Int8; code; int8OfNat; int8Roundtrip; zero8; one8 )
open import Exotic.ERL.Canonical.CanonicalOptimizer using (CanonicalConfig; canonical)
open import Exotic.ERL.Finite.Activation using (softsignQ8; cReLU8)
open import Exotic.ERL.Finite.TrueOnlineTD using
  ( TrueOnlineState; initialState; exampleFeature; exampleNextFeature; learnerStep )
open import Exotic.ERL.Exploration.FiniteNoise using
  ( Noise; neg; zero; pos; weight; sumWeights; totalWeight; zeroHasPositiveMass )
open import Exotic.ERL.Exploration.NoisyNetFinite using (perturbScalar)
open import Exotic.ERL.Exploration.FiniteMarkov using (selfLoopExample)
open import Exotic.ERL.Exploration.ComposedLearnerExploration using
  ( composedExploreStep; zeroStep; zeroStep-is-initial )
open import Exotic.ERL.Exploration.DyadicOpenES using
  ( openESMutation; openESZeroSelfLoop )
open import Exotic.ERL.Exploration.DyadicMR15GA using
  ( Population; Coordinate; Noise; StepGate
  ; noPerturb; perturb; mutation; zeroPopulation
  ; noPerturbation-self-loop; canonicalZero-self-loop )
open import Exotic.ERL.Exploration.TheoremObligations using
  ( SelfLoop; canonicalNoiseStep; canonicalNoiseSelfLoop
  ; openESStep; openESSelfLoop; mr15Step; mr15SelfLoop
  ; MR15AperiodicityObligation )
open import Exotic.ERL.Exploration.MR15OneBit using
  ( BitState; oneBitSupport; oneBitSelfLoop )
open import Exotic.ERL.Representation.HaarInt8 using ( H8; double8; H8-square )
open import Exotic.ERL.FullCoupled.FiniteLearningCertificate using
  ( LearnState; prediction; trainingWitness; trainedWitness
  ; trainingWitness-learns; trainingWitness-nonempty; trainingWitness-target )
open import Exotic.ERL.FullCoupled.FiniteLearner using
  ( Parameters; parameters; Token; token; Window2; window2; learnForward )
open import Exotic.ERL.FullCoupled.SharedActorCritic using
  ( ActorCriticParameters; representation; actorForward; criticForward
  ; sharedRepresentation; sharedActorCriticAgreement
  ; sampleSharedParameters; sampleActorOutput; sampleCriticOutput )


testInt8Roundtrip : ∀ (x : Int8) →
  toℕ (code (int8OfNat (toℕ (code x)))) ≡ toℕ (code x)
testInt8Roundtrip x = int8Roundtrip x

testCanonicalConfig : CanonicalConfig
testCanonicalConfig = canonical

testNoiseWeights : sumWeights 31 ≡ 256
testNoiseWeights = totalWeight

testNoiseZeroMass : weight zero ≡ 16
testNoiseZeroMass = zeroHasPositiveMass

testNoiseUnitMinus : perturbScalar neg one8 ≡ zero8
testNoiseUnitMinus = refl

testNoiseUnitPlus : perturbScalar pos zero8 ≡ one8
testNoiseUnitPlus = refl

testZeroPerturbation : perturbScalar zero one8 ≡ one8
testZeroPerturbation = selfLoopExample

testOpenESZeroPerturbation : openESMutation zero one8 ≡ one8
testOpenESZeroPerturbation = openESZeroSelfLoop

testCanonicalNoiseSelfLoop : SelfLoop canonicalNoiseStep
testCanonicalNoiseSelfLoop = canonicalNoiseSelfLoop

testOpenESSelfLoop : SelfLoop openESStep
testOpenESSelfLoop = openESSelfLoop

testMR15SelfLoop : SelfLoop mr15Step
testMR15SelfLoop = mr15SelfLoop

testMR15NoPerturbation : ∀ (n : Noise) (j : Coordinate) (p : Population) →
  mutation noPerturb n j p ≡ p
testMR15NoPerturbation = noPerturbation-self-loop

testMR15CanonicalZero : ∀ (j : Coordinate) (p : Population) →
  mutation perturb zero j p ≡ p
testMR15CanonicalZero = canonicalZero-self-loop

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

testOneBitSelfLoop : Σ BitState (λ s → oneBitSupport s s)
testOneBitSelfLoop = oneBitSelfLoop

testSharedRepresentation : ∀ (p : ActorCriticParameters) (w : Window2) →
  sharedRepresentation (representation p) w ≡ sharedRepresentation (representation p) w
testSharedRepresentation = sharedActorCriticAgreement

testSharedActorOutput : Int8
testSharedActorOutput = sampleActorOutput

testSharedCriticOutput : Int8
testSharedCriticOutput = sampleCriticOutput

testActorForward : Int8
testActorForward = actorForward sampleSharedParameters sampleWindow

testCriticForward : Int8
testCriticForward = criticForward sampleSharedParameters sampleWindow

testLearningState : LearnState
testLearningState = trainedWitness
testLearningNonempty : prediction trainingWitness ≡ zero8
testLearningNonempty = trainingWitness-nonempty
testLearningExact : prediction trainedWitness ≡ int8OfNat 4
testLearningExact = trainingWitness-learns
testLearningTargetValue : LearnState.target trainingWitness ≡ int8OfNat 4
testLearningTargetValue = trainingWitness-target
