{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.GRUPerturbationMethods where

open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Aperiodic
  ; Irreducible
  ; PeriodOne
  ; SelfLoop
  ; periodOne-from-components
  ; a-periodic-from-components
  ; Reach
  ; there
  ; here
  )
open import Exotic.ERL.FullCoupled.GRUNoisyNetState using
  ( GRUNoisyNetState
  ; GRUNoisyStep
  ; gruNoisyStepFromFreshNoise
  ; gruNoiseForState
  ; hiddenState
  )

-- The three named explorators now share the same finite GRU carrier. The
-- current theorem authority proves their common fresh-target recurrence shell;
-- a strict ordering requires explicit carrier maps and proper fibers for the
-- concrete perturbation semantics and is therefore not asserted here.
data GRUPerturbationMethod : Set where
  gruOpenES gruMR15 gruNoisyNet : GRUPerturbationMethod

GRUStep : GRUPerturbationMethod → GRUNoisyNetState → GRUNoisyNetState → Set
GRUStep _ = GRUNoisyStep

gruFreshStep : ∀ (m : GRUPerturbationMethod)
  {s : GRUNoisyNetState} (t : GRUNoisyNetState)
  → GRUStep m s t
gruFreshStep m t =
  gruNoisyStepFromFreshNoise (gruNoiseForState t) (hiddenState t)

gruIrreducible : ∀ (m : GRUPerturbationMethod) → Irreducible (GRUStep m)
gruIrreducible m s t =
  there (gruFreshStep m t) here

gruSelfLoop : ∀ (m : GRUPerturbationMethod) → SelfLoop (GRUStep m)
gruSelfLoop m s = gruFreshStep m s

gruPeriodOne : ∀ (m : GRUPerturbationMethod) → PeriodOne (GRUStep m)
gruPeriodOne m =
  periodOne-from-components (gruIrreducible m) (gruSelfLoop m)

gruAperiodic : ∀ (m : GRUPerturbationMethod) → Aperiodic (GRUStep m)
gruAperiodic m =
  a-periodic-from-components (gruIrreducible m) (gruSelfLoop m)
