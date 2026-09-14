{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteMarkovComposition where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; there
  ; here
  ; Irreducible
  ; PeriodOne
  ; SelfLoop
  ; periodOne-from-components
  )
open import Exotic.ERL.Exploration.DyadicLaws using
  ( Law
  ; Method
  ; flatDyadic
  ; mr15GA
  ; openES
  ; noisyNetGRU
  )
open import Exotic.ERL.FullCoupled.DyadicMethodLawCoupling using
  ( CanonicalState
  ; CoupledStep
  ; coupledIrreducible
  ; coupledPeriodOne
  ; coupledSelfLoop
  )

------------------------------------------------------------------------
-- Exact boundary of the current formalization.
-- `CoupledStep` is a finite support relation. Its reachability and
-- period-one laws are genuine, but a support relation alone is not a
-- stochastic kernel and therefore does not prove invariant-measure
-- existence, uniqueness, or convergence.
------------------------------------------------------------------------

mr15SupportIrreducible :
  Irreducible (CoupledStep flatDyadic mr15GA)
mr15SupportIrreducible = coupledIrreducible mr15GA

openESSupportIrreducible :
  Irreducible (CoupledStep flatDyadic openES)
openESSupportIrreducible = coupledIrreducible openES

noisyNetSupportIrreducible :
  Irreducible (CoupledStep flatDyadic noisyNetGRU)
noisyNetSupportIrreducible = coupledIrreducible noisyNetGRU

mr15SupportPeriodOne :
  PeriodOne (CoupledStep flatDyadic mr15GA)
mr15SupportPeriodOne = coupledPeriodOne mr15GA

openESSupportPeriodOne :
  PeriodOne (CoupledStep flatDyadic openES)
openESSupportPeriodOne = coupledPeriodOne openES

noisyNetSupportPeriodOne :
  PeriodOne (CoupledStep flatDyadic noisyNetGRU)
noisyNetSupportPeriodOne = coupledPeriodOne noisyNetGRU

------------------------------------------------------------------------
-- This is the clean place for a genuine noise/exploration support law:
-- it sits at the transition boundary and can feed a deterministic GRU map.
-- Full support gives irreducibility and a self-loop gives period one.
------------------------------------------------------------------------

record FullSupportNoise (S : Set) : Set₁ where
  constructor fullSupportNoise
  field
    support : S → S → Set
    full-support : ∀ x y → support x y
    self-support : ∀ x → support x x

open FullSupportNoise public

noise-support-irreducible :
  ∀ {S : Set} (N : FullSupportNoise S) →
  Irreducible (support N)
noise-support-irreducible N x y = there (full-support N x y) here

noise-support-period-one :
  ∀ {S : Set} (N : FullSupportNoise S) →
  PeriodOne (support N)
noise-support-period-one N =
  periodOne-from-components
    (noise-support-irreducible N)
    (self-support N)

------------------------------------------------------------------------
-- Deterministic counterexample: noise is not required for a Markov chain
-- to exist, but deterministic finite dynamics do not automatically give the
-- irreducible + period-one combination used by the repository.
------------------------------------------------------------------------

data Two : Set where
  leftState : Two
  rightState : Two

toggle : Two → Two
toggle leftState = rightState
toggle rightState = leftState

toggleStep : Two → Two → Set
toggleStep x y = toggle x ≡ y

not-left-right-eq : rightState ≢ leftState
not-left-right-eq ()

notToggleSelfLoop :
  ¬ (∀ x → toggleStep x x)
notToggleSelfLoop self =
  not-left-right-eq (self leftState)

notTogglePeriodOne :
  ¬ PeriodOne toggleStep
notTogglePeriodOne p =
  notToggleSelfLoop (PeriodOne.selfLoop p)

------------------------------------------------------------------------
-- Therefore the broad claim "deterministic GRU + finite carrier implies
-- Markovian ergodicity" is false. The existing finite support laws must be
-- accompanied by an actual normalized stochastic kernel if invariant-measure
-- and convergence theorems are desired.
------------------------------------------------------------------------

fullCompositionMarkovErgodicityNotAutomatic :
  ¬ (∀ (S : Set) (step : S → S) →
      PeriodOne (λ x y → step x ≡ y))
fullCompositionMarkovErgodicityNotAutomatic witness =
  notTogglePeriodOne (witness Two toggle)
