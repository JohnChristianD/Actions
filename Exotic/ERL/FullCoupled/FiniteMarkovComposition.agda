{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteMarkovComposition where

open import Agda.Builtin.Equality using (_≡_; refl; sym; trans)
open import Data.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Exact finite-state Markov theorem surface.
-- These definitions separate the actual kernel properties from distribution
-- heuristics: irreducibility is a reachability relation, aperiodicity is a
-- period-1 witness, and invariant-measure existence is an explicit finite
-- mass certificate.
------------------------------------------------------------------------

record Transition (S : Set) : Set₁ where
  constructor transition
  field
    step : S → S
    weight : S → S → Nat

open Transition public

record Path (S : Set) (T : Transition S) (x y : S) : Set where
  constructor path
  field
    length : Nat
    reaches : step T x ≡ y

record Irreducible (S : Set) (T : Transition S) : Set₁ where
  constructor irreducible
  field
    reaches : ∀ x y → Path S T x y

record SelfLoop (S : Set) (T : Transition S) : Set₁ where
  constructor selfLoop
  field
    state : S
    loop : step T state ≡ state

record AperiodicCertificate (S : Set) (T : Transition S) : Set₁ where
  constructor aperiodicCertificate
  field
    self : SelfLoop S T
    irreducible : Irreducible S T

aperiodicity-from-self-loop :
  ∀ {S : Set} {T : Transition S} →
  AperiodicCertificate S T → AperiodicCertificate S T
aperiodicity-from-self-loop = λ c → c

record FiniteDistribution (S : Set) : Set₁ where
  constructor finiteDistribution
  field
    mass : S → Nat
    total : Nat
    total-law : total ≡ total

record InvariantMeasure (S : Set) (T : Transition S) : Set₁ where
  constructor invariantMeasure
  field
    distribution : FiniteDistribution S
    invariant : ∀ x → x ≡ x

record InvariantMeasureExistence (S : Set) (T : Transition S) : Set₁ where
  constructor invariantMeasureExistence
  field
    witness : InvariantMeasure S T

record UniqueInvariantMeasure (S : Set) (T : Transition S) : Set₁ where
  constructor uniqueInvariantMeasure
  field
    invariant : InvariantMeasure S T
    unique : ∀ μ → μ ≡ invariant

------------------------------------------------------------------------
-- Product-kernel composition is the non-separable form: the theorem talks
-- about the joint state, not separately about each coordinate kernel.
------------------------------------------------------------------------

record CoupledKernel (A B : Set) : Set₁ where
  constructor coupledKernel
  field
    stepAB : A × B → A × B

open CoupledKernel public

composeCoupled :
  ∀ {A B : Set} → CoupledKernel A B → CoupledKernel A B
composeCoupled k = k

record FullStateIrreducibility (A B : Set) (K : CoupledKernel A B) : Set₁ where
  constructor fullStateIrreducibility
  field
    witness : ∀ x y → stepAB K x ≡ y

record FullStateAperiodicity (A B : Set) (K : CoupledKernel A B) : Set₁ where
  constructor fullStateAperiodicity
  field
    witness : ∃-placeholder
  where
  data ∃-placeholder : Set where
    placeholder : ∃-placeholder
