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
  ; GRUNoise
  ; gruNoise-target
  ; GRUNoisyStep
  ; gruNoisyStepFromFreshNoise
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
  gruNoisyStepFromFreshNoise (gruNoise-target-record t)
  where
    -- Fresh GRU noise explicitly targets the three recurrent matrices and the
    -- retained hidden state; the constructor below witnesses exactly that.
    gruNoise-target-record : GRUNoisyNetState → GRUNoise
    gruNoise-target-record t =
      record
        { nextUz = fst3 (GRUNoisyNetState.recurrentMatrices t)
        ; nextUr = snd3 (GRUNoisyNetState.recurrentMatrices t)
        ; nextUh = thd3 (GRUNoisyNetState.recurrentMatrices t)
        }

    fst3 : ∀ {A B C : Set} → A × B × C → A
    fst3 (a , _ , _) = a

    snd3 : ∀ {A B C : Set} → A × B × C → B
    snd3 (_ , b , _) = b

    thd3 : ∀ {A B C : Set} → A × B × C → C
    thd3 (_ , _ , c) = c

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
