{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalErgodicity where

open import Data.Nat using (suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8OfNat
  ; zero8
  )
open import Exotic.ERL.Exploration.FiniteNoise using
  ( Noise
  ; neg
  ; zero
  ; pos
  ; weight
  ; noiseCode
  ; totalWeight
  ; zeroHasPositiveMass
  ; unitMinusWitness
  ; unitPlusWitness
  )
open import Exotic.ERL.FullCoupled.CanonicalToken using
  ( Token
  ; token
  )
open import Exotic.ERL.FullCoupled.CanonicalLearner using
  ( LearnerState
  ; start
  ; step
  )
open import Exotic.ERL.FullCoupled.FiniteAperiodicity using
  ( []ᵖ
  ; _∷ᵖ_
  ; ExactReach
  ; exactHere
  ; exactTrans
  ; Irreducible
  ; AperiodicViaConsecutiveReturns
  ; hubAperiodicity
  )

noiseWeightPos : weight zero ≡ 16
noiseWeightPos = zeroHasPositiveMass

negativeUnit : noiseCode neg ≡ int8OfNat 255
negativeUnit = unitMinusWitness

positiveUnit : noiseCode pos ≡ int8OfNat 1
positiveUnit = unitPlusWitness

zeroUnit : noiseCode zero ≡ zero8
zeroUnit = refl

normalisation : totalWeight ≡ 256
normalisation = totalWeight

data CanonicalStep : LearnerState → LearnerState → Set where
  edge : ∀ {s}
    (epsilon nextEpsilon : Noise)
    (a b : Token)
    (reward : Int8) →
    CanonicalStep s
      (step s epsilon nextEpsilon a b reward)

data JointReach : LearnerState → LearnerState → Set where
  here : ∀ {s} → JointReach s s
  there : ∀ {s t u} →
    CanonicalStep s t →
    JointReach t u →
    JointReach s u

toExactReach : ∀ {s t : LearnerState} →
  JointReach s t → ExactReach CanonicalStep s t
toExactReach here = exactHere
toExactReach (there e r) =
  exactTrans
    (suc 0 , e ∷ᵖ []ᵖ)
    (toExactReach r)

record JointIrreducibilityWitness : Set₁ where
  field
    reachable : ∀ (s t : LearnerState) → JointReach s t

record FullStateSelfLoop : Set where
  constructor selfLoop
  field
    at : LearnerState
    holds : CanonicalStep at at

startSelfLoop : FullStateSelfLoop
startSelfLoop =
  selfLoop
    start
    (edge
      zero zero
      (token zero8 zero8 zero8 zero8)
      (token zero8 zero8 zero8 zero8)
      zero8)

canonicalIrreducibility :
  JointIrreducibilityWitness →
  Irreducible CanonicalStep
canonicalIrreducibility witness =
  record
    { reach = λ s t →
        toExactReach (JointIrreducibilityWitness.reachable witness s t)
    }

canonicalAperiodicity :
  JointIrreducibilityWitness →
  AperiodicViaConsecutiveReturns CanonicalStep
canonicalAperiodicity witness =
  hubAperiodicity
    (canonicalIrreducibility witness)
    (record
      { hub = FullStateSelfLoop.at startSelfLoop
      ; loop = FullStateSelfLoop.holds startSelfLoop
      })
