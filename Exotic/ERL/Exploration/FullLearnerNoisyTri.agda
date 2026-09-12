{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.FullLearnerNoisyTri where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8; int8Add; one8; zero8)
open import Exotic.ERL.Exploration.FiniteNoise using (Noise; neg; zero; pos)
open import Exotic.ERL.FullCoupled.FiniteLearner using
  ( Parameters
  ; Window2
  ; Parameters.w1
  ; Parameters.w2
  ; Parameters.w3
  ; Parameters.w4
  ; Parameters.w5
  ; Parameters.outputProjection
  ; parameters
  ; learnForward
  )

perturbParameters : Noise → Parameters → Parameters
perturbParameters neg p = parameters
  (w1 p) (w2 p) (w3 p) (w4 p) (int8Add (w5 p) (int8Add one8 one8))
  (outputProjection p)
perturbParameters zero p = p
perturbParameters pos p = parameters
  (w1 p) (w2 p) (w3 p) (w4 p) (int8Add (w5 p) one8)
  (outputProjection p)

noisyTriForward : Noise → Parameters → Window2 → Int8
noisyTriForward noise p w = learnForward (perturbParameters noise p) w

zeroNoisePreservesLearner : ∀ (p : Parameters) (w : Window2) →
  noisyTriForward zero p w ≡ learnForward p w
zeroNoisePreservesLearner p w = refl

positiveNoiseChangesParameter : ∀ (p : Parameters) →
  perturbParameters pos p ≡
  parameters
    (w1 p) (w2 p) (w3 p) (w4 p)
    (int8Add (w5 p) one8)
    (outputProjection p)
positiveNoiseChangesParameter p = refl
