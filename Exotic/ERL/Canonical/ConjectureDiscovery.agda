{-# OPTIONS --safe #-}

module Exotic.ERL.Canonical.ConjectureDiscovery where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (toℕ)
open import Data.Nat using (_≤_; _+_; _*_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8OfNat
  ; int8Roundtrip
  ; one8
  ; zero8
  )
open import Exotic.ERL.Exploration.FiniteNoise using
  ( Noise
  ; weight
  ; neg
  ; zero
  ; pos
  ; totalWeight
  ; zeroHasPositiveMass
  ; unitMinusWitness
  ; unitPlusWitness
  )
open import Exotic.ERL.Exploration.CanonicalMR15GA using
  ( populationSize
  ; dimension
  ; oneFifthStepUpdate
  ; lowerExponent
  ; raiseExponent
  ; initialExponent
  )
open import Exotic.ERL.FullCoupled.CanonicalLearner using
  ( LearnerState
  ; start
  ; step
  ; zeroSelfLoop
  )
open import Exotic.ERL.FullCoupled.CanonicalLearnerEA using
  ( CoupledState
  ; startCoupled
  ; coupledStep
  ; noPerturb
  ; zeroNoiseTape
  ; zeroCoordinateTape
  )
open import Exotic.ERL.FullCoupled.FiniteAperiodicity using
  ( ExactReach
  ; SelfLoop
  ; Irreducible
  ; AperiodicViaConsecutiveReturns
  ; hubAperiodicity
  )

DtriNormalises :
totalWeight ≡ 256
DtriNormalises = totalWeight

DtriZeroMass :
weight zero ≡ 16
DtriZeroMass = zeroHasPositiveMass

DtriMinusUnit :
  let _ = neg
  in weight neg ≡ 15
DtriMinusUnit = refl

DtriPlusUnit :
  let _ = pos
  in weight pos ≡ 15
DtriPlusUnit = refl

DtriUnitCodes :
  noiseCodeNeg × noiseCodePos
  where
  noiseCodeNeg : Noise → Int8
  noiseCodeNeg n = int8OfNat (toℕ n + 241)
  noiseCodePos : Noise → Int8
  noiseCodePos n = int8OfNat (toℕ n + 241)

oneFifthExactAtThree :
oneFifthStepUpdate initialExponent (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
  ≡ lowerExponent initialExponent
oneFifthExactAtThree = refl

oneFifthExactAtFour :
oneFifthStepUpdate initialExponent (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
  ≡ raiseExponent initialExponent
oneFifthExactAtFour = refl

populationAxisCount :
populationSize * dimension ≡ 64
populationAxisCount = refl

canonicalLearnerSelfLoop :
  step start zero zero
    (token zero8 zero8 zero8 zero8)
    (token zero8 zero8 zero8 zero8)
    zero8
  ≡ start
canonicalLearnerSelfLoop = zeroSelfLoop

canonicalComposedSelfLoop :
  coupledStep
    startCoupled
    noPerturb
    zero
    zero
    zeroNoiseTape
    zeroCoordinateTape
    zero8
  ≡ startCoupled
canonicalComposedSelfLoop = refl
