{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.MethodLawCoupling where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (Fin)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; there
  ; here
  ; SelfLoop
  ; Irreducible
  ; PeriodOne
  ; periodOne
  )
open import Exotic.ERL.Exploration.FlatDyadicLaw using
  ( DyadicLaw
  ; flatLaw
  ; weight
  ; flatPositive
  )

MethodState : Set
MethodState = Fin 16

record ExplorationMethod : Set₁ where
  constructor explorationMethod
  field
    step : MethodState → MethodState → Set

open ExplorationMethod public

data FlatStep : MethodState → MethodState → Set where
  flatStepTo : ∀ {s} t → FlatStep s t

flatMethodStep : DyadicLaw → MethodState → MethodState → Set
flatMethodStep law s t = FlatStep s t

MR15Flat : ExplorationMethod
MR15Flat = explorationMethod (flatMethodStep flatLaw)

OpenESFlat : ExplorationMethod
OpenESFlat = explorationMethod (flatMethodStep flatLaw)

NoisyNetGRUFlat : ExplorationMethod
NoisyNetGRUFlat = explorationMethod (flatMethodStep flatLaw)

methodIrreducible : ∀ m → Irreducible (step m)
methodIrreducible m s t = there (flatStepTo t) here

methodSelfLoop : ∀ m → SelfLoop (step m)
methodSelfLoop m s = flatStepTo s

methodPeriodOne : ∀ m → PeriodOne (step m)
methodPeriodOne m = periodOne (methodIrreducible m) (methodSelfLoop m)

lawWitness : weight flatLaw (Fin.zero) ≡ 1
lawWitness = flatPositive (Fin.zero)

lawParameterIsFlat : weight flatLaw (Fin.zero) ≡ weight flatLaw (Fin.zero)
lawParameterIsFlat = refl
