{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.LatticeReachability where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ)
open import Exotic.ERL.Exploration.CanonicalMR15GA using
  ( Coordinate
  ; Genome
  ; Population
  ; Fitness
  ; MR15State
  ; StepGate
  ; Noise
  ; mutateGenome
  ; generationStep
  ; initialExponent
  )
open import Exotic.ERL.Exploration.FiniteNoise using
  ( pos
  ; neg
  )
open import Exotic.ERL.FullCoupled.CanonicalLearnerEA using
  ( CoupledState
  ; CoupledReach
  ; CoupledIrreducibility
  ; coupledIrreducibility
  ; coupledAperiodicity
  ; CoupledEdge
  )
open import Exotic.ERL.FullCoupled.FiniteAperiodicity using
  ( ExactReach
  ; AperiodicViaConsecutiveReturns
  )

data GenomeStep : Genome → Genome → Set where
  plus : ∀ (g : Genome) (j : Coordinate) →
    GenomeStep g (mutateGenome initialExponent pos j g)
  minus : ∀ (g : Genome) (j : Coordinate) →
    GenomeStep g (mutateGenome initialExponent neg j g)

data GenomeReach : Genome → Genome → Set where
  here : ∀ {g} → GenomeReach g g
  there : ∀ {g h k} →
    GenomeStep g h →
    GenomeReach h k →
    GenomeReach g k

GenomeLatticeReachabilityObligation : Set
GenomeLatticeReachabilityObligation =
  ∀ (g h : Genome) → GenomeReach g h

data EAEdge : MR15State → MR15State → Set where
  edge : ∀ {s}
    (fit : Fitness)
    (gate : StepGate)
    (noises : (Fin 16) → Noise)
    (coords : (Fin 16) → Coordinate) →
    EAEdge s (generationStep fit gate s noises coords)

data EAReach : MR15State → MR15State → Set where
  here : ∀ {s} → EAReach s s
  there : ∀ {s t u} →
    EAEdge s t →
    EAReach t u →
    EAReach s u

EAStateReachabilityObligation : Set
EAStateReachabilityObligation =
  ∀ (s t : MR15State) → EAReach s t

FullCoupledReachabilityObligation : Set
FullCoupledReachabilityObligation =
  CoupledIrreducibility

fullCoupledIrreducibility :
  FullCoupledReachabilityObligation →
  ∀ (s t : CoupledState) → CoupledReach s t
fullCoupledIrreducibility h = h

fullCoupledAperiodicity :
  FullCoupledReachabilityObligation →
  AperiodicViaConsecutiveReturns CoupledEdge
fullCoupledAperiodicity h =
  coupledAperiodicity h .witness
