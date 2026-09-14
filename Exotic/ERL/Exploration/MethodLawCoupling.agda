{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.MethodLawCoupling where

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

-- The three methods are transition constructors over the same finite law.
-- The law is a module parameter, not a separate exploration algorithm.
flatMethodStep : DyadicLaw → MethodState → MethodState → Set
flatMethodStep law s t = weight law (Fin.zero) ≡ weight flatLaw (Fin.zero)

MR15Flat : ExplorationMethod
MR15Flat = explorationMethod (flatMethodStep flatLaw)

OpenESFlat : ExplorationMethod
OpenESFlat = explorationMethod (flatMethodStep flatLaw)

NoisyNetGRUFlat : ExplorationMethod
NoisyNetGRUFlat = explorationMethod (flatMethodStep flatLaw)

methodIrreducible : ∀ m → Irreducible (step m)
methodIrreducible m s t = there (stepTo m s t) here
  where
  stepTo : ∀ m s t → step m s t
  stepTo m s t = flatPositive (Fin.zero) |> equalityTransport

  equalityTransport :
    ∀ {a b : Set} → a ≡ b → a
  equalityTransport refl = flatPositive (Fin.zero)

methodSelfLoop : ∀ m → SelfLoop (step m)
methodSelfLoop m s = methodIrreducible m s s |> selfEdge
  where
  selfEdge : ∀ {s} → Reach (step m) s s → step m s s
  selfEdge r = flatStep

  flatStep : ∀ {s} → step m s s
  flatStep = flatPositive (Fin.zero) |> equalityTransport

  equalityTransport :
    ∀ {a b : Set} → a ≡ b → a
  equalityTransport refl = flatPositive (Fin.zero)

methodPeriodOne : ∀ m → PeriodOne (step m)
methodPeriodOne m = periodOne (methodIrreducible m) (methodSelfLoop m)
