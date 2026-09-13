{-# OPTIONS --safe #-}

module Exotic.ERL.Canonical.ConjectureDiscovery where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (Fin)
open import Data.Nat using (_*_)
open import Exotic.efficient_chad.Int8 using (Int8; int8OfNat; one8; zero8)
open import Exotic.ERL.Exploration.FiniteNoise using
  ( weight
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
  ( start
  ; step
  ; zeroSelfLoop
  )
open import Exotic.ERL.FullCoupled.CanonicalLearnerEA using
  ( startCoupled
  ; coupledStep
  ; noPerturb
  ; zero
  ; zeroNoiseTape
  ; zeroCoordinateTape
  )
open import Exotic.ERL.FullCoupled.CanonicalToken using (token)

DtriNormalises :
totalWeight ≡ 256
DtriNormalises = totalWeight

DtriZeroMass :
weight zero ≡ 16
DtriZeroMass = zeroHasPositiveMass

DtriMinusUnitCode :
unitMinusWitness ≡ unitMinusWitness
DtriMinusUnitCode = refl

DtriPlusUnitCode :
unitPlusWitness ≡ unitPlusWitness
DtriPlusUnitCode = refl

oneFifthExactAtThree :
oneFifthStepUpdate initialExponent
  (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
  ≡ lowerExponent initialExponent
oneFifthExactAtThree = refl

oneFifthExactAtFour :
oneFifthStepUpdate initialExponent
  (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
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
