{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.FiniteLearningCertificate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8Add
  ; int8OfNat
  ; code
  ; zero8
  )
open import Data.Fin using (toℕ)
open import Data.Nat using (_∸_)
open import Data.Nat.Properties using (_≤?_; yes; no)

negate8 : Int8 → Int8
negate8 x = int8OfNat (256 ∸ toℕ (code x))

qProject3 : Int8 → Int8
qProject3 x with toℕ (code x) ≤? 3
... | yes _ = zero8
... | no _ = x

record LearnState : Set where
  constructor learnState
  field
    parameter target : Int8

prediction : LearnState → Int8
prediction s = LearnState.parameter s

tdError : LearnState → Int8
tdError s = int8Add (LearnState.target s) (negate8 (prediction s))

update : LearnState → LearnState
update s = learnState
  (int8Add (LearnState.parameter s) (qProject3 (tdError s)))
  (LearnState.target s)

trainingWitness : LearnState
trainingWitness = learnState zero8 (int8OfNat 4)

trainedWitness : LearnState
trainedWitness = update trainingWitness

trainingWitness-learns : prediction trainedWitness ≡ int8OfNat 4
trainingWitness-learns = refl

trainingWitness-nonempty : prediction trainingWitness ≡ zero8
trainingWitness-nonempty = refl

trainingWitness-target : LearnState.target trainingWitness ≡ int8OfNat 4
trainingWitness-target = refl
