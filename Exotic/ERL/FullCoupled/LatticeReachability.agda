{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.LatticeReachability where

open import Data.Fin using (Fin)
open import Data.Product using (_×_)
open import Exotic.ERL.Exploration.CanonicalMR15GA using
  ( Coordinate
  ; Genome
  ; Population
  ; MR15State
  ; StepGate
  ; Exponent
  ; Successes
  ; mutateGenome
  ; generationStep
  ; initialExponent
  ; initialMR15
  )
open import Exotic.ERL.Exploration.FiniteNoise using
  ( Noise
  ; pos
  ; neg
  ; zero
  )
open import Exotic.ERL.FullCoupled.CanonicalLearnerEA using
  ( CoupledState
  ; CoupledReach
  ; CoupledIrreducibility
  ; coupledIrreducibility
  ; coupledAperiodicity
  )
open import Exotic.ERL.FullCoupled.FiniteAperiodicity using
  ( Irreducible
  ; AperiodicViaConsecutiveReturns
  )

CoordinateLatticeReachability : Set
CoordinateLatticeReachability =
  ∀ (g h : Genome) →
  ∀ (j : Coordinate) →
  ∀ (n : Noise) →
  mutateGenome initialExponent n j g ≡ mutateGenome initialExponent n j h

UnitCoordinateSupport : Set
UnitCoordinateSupport =
  ∀ (g : Genome) (j : Coordinate) →
  (mutateGenome initialExponent pos j g ,
   mutateGenome initialExponent neg j g)
  ≡
  (mutateGenome initialExponent pos j g ,
   mutateGenome initialExponent neg j g)

EAStateReachability : Set
EAStateReachability =
  ∀ (s t : MR15State) →
  ∃λ (n : _) →
  s ≡ t

FullCoupledIrreducibility : Set
FullCoupledIrreducibility =
  CoupledIrreducibility

fullCoupledAperiodicity :
  FullCoupledIrreducibility →
  AperiodicViaConsecutiveReturns _
fullCoupledAperiodicity reach =
  CoupledAperiodicity.witness (coupledAperiodicity reach)
