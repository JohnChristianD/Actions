{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalErgodicity where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8OfNat
  ; int8Add
  ; zero8
  )
open import Exotic.ERL.Exploration.FiniteNoise using
  ( Noise
  ; neg
  ; zero
  ; pos
  ; weight
  ; totalWeight
  ; zeroHasPositiveMass
  ; unitMinusWitness
  ; unitPlusWitness
  )
open import Exotic.ERL.Exploration.NoisyNetFinite using (noiseDelta)
open import Exotic.ERL.FullCoupled.CanonicalToken using
  ( Token
  ; token
  )
open import Exotic.ERL.FullCoupled.CanonicalLearner using
  ( LearnerState
  ; start
  ; step
  ; zeroSelfLoop
  )

noiseWeightPos : weight zero ≡ 16
noiseWeightPos = zeroHasPositiveMass

negativeUnit : noiseDelta neg ≡ int8OfNat 255
negativeUnit = unitMinusWitness

positiveUnit : noiseDelta pos ≡ int8OfNat 1
positiveUnit = unitPlusWitness

zeroUnit : noiseDelta zero ≡ zero8
zeroUnit = refl

normalisation : totalWeight ≡ 256
normalisation = totalWeight

data NoiseReach : Int8 → Int8 → Set where
  here : ∀ {x} → NoiseReach x x
  plus : ∀ {x y} →
    y ≡ int8Add x (noiseDelta pos) →
    NoiseReach y x →
    NoiseReach x y
  minus : ∀ {x y} →
    y ≡ int8Add x (noiseDelta neg) →
    NoiseReach y x →
    NoiseReach x y

localPlusWitness : ∀ x → NoiseReach x (int8Add x (noiseDelta pos))
localPlusWitness x = plus refl here

localMinusWitness : ∀ x → NoiseReach x (int8Add x (noiseDelta neg))
localMinusWitness x = minus refl here

data JointReach : LearnerState → LearnerState → Set where
  here : ∀ {s} → JointReach s s
  there : ∀ {s t u epsilon nextEpsilon : Noise}
    {a b : Token}
    {reward : Int8} →
    step s epsilon nextEpsilon a b reward ≡ t →
    JointReach t u →
    JointReach s u

record SelfLoop : Set where
  constructor selfLoop
  field
    at : LearnerState
    holds :
      step at zero zero
        (token zero8 zero8 zero8 zero8)
        (token zero8 zero8 zero8 zero8)
        zero8
      ≡ at

startSelfLoop : SelfLoop
startSelfLoop = selfLoop start zeroSelfLoop

record JointIrreducibilityWitness : Set₁ where
  field
    reachable : ∀ (s t : LearnerState) → JointReach s t

record JointAperiodicityWitness : Set₁ where
  field
    irreducible : JointIrreducibilityWitness
    selfLoop : SelfLoop

conditionalAperiodicity :
  JointIrreducibilityWitness →
  SelfLoop →
  JointAperiodicityWitness
conditionalAperiodicity ir loop =
  record
    { irreducible = ir
    ; selfLoop = loop
    }
