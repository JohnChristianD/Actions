{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.ComposedLearnerExploration where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8; zero8; one8)
open import Exotic.ERL.Finite.Int8Vector using (Int8Vector4; vec4)
open import Exotic.ERL.Finite.ComposedLearner using (composedSoftsignStep)
open import Exotic.ERL.Finite.TrueOnlineTD using
  ( TrueOnlineState
  ; trueOnlineState
  ; theta
  ; trace
  ; previousFeature
  ; previousValue
  ; initialState
  )
open import Exotic.ERL.Exploration.FiniteNoise using (Noise; neg; zero; pos)
open import Exotic.ERL.Exploration.NoisyNetFinite using (perturbVector4)

exploreState : Noise → TrueOnlineState → TrueOnlineState
exploreState zero s = s
exploreState neg s = trueOnlineState
  (perturbVector4 neg (theta s))
  (trace s)
  (previousFeature s)
  (previousValue s)
exploreState pos s = trueOnlineState
  (perturbVector4 pos (theta s))
  (trace s)
  (previousFeature s)
  (previousValue s)

composedExploreStep :
  Noise → Int8 → Int8Vector4 → Int8Vector4 → TrueOnlineState → TrueOnlineState
composedExploreStep noise reward phi nextPhi state =
  exploreState noise
    (composedSoftsignStep reward phi nextPhi state)

zeroFeature : Int8Vector4
zeroFeature = vec4 zero8 zero8 zero8 zero8

zeroStep : TrueOnlineState
zeroStep =
  composedExploreStep zero zero8 zeroFeature zeroFeature initialState

zeroStep-is-initial : zeroStep ≡ initialState
zeroStep-is-initial = refl

zeroExploration-is-learner : ∀
  (reward : Int8) (phi nextPhi : Int8Vector4) (state : TrueOnlineState) →
  composedExploreStep zero reward phi nextPhi state
    ≡ composedSoftsignStep reward phi nextPhi state
zeroExploration-is-learner reward phi nextPhi state = refl
