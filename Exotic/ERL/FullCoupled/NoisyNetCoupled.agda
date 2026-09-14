{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.NoisyNetCoupled where

open import Exotic.ERL.Exploration.DyadicLaws using
  ( Law
  ; noisyNetGRU
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Irreducible
  ; SelfLoop
  ; PeriodOne
  )
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; gruStep
  ; gruGlobalControlPersists
  )
open import Exotic.ERL.FullCoupled.DyadicMethodLawCoupling using
  ( CoupledStep
  ; coupledIrreducible
  ; coupledSelfLoop
  ; coupledPeriodOne
  ; RecurrentProjection
  ; noisyNetProjection
  ; noisyNet-project-lift
  )

NoisyNetState : Set
NoisyNetState = GRUState

noisyNetGRUIrreducible :
  ∀ (l : Law) → Irreducible (CoupledStep l noisyNetGRU)
noisyNetGRUIrreducible l = coupledIrreducible l noisyNetGRU

noisyNetGRUSelfLoop :
  ∀ (l : Law) → SelfLoop (CoupledStep l noisyNetGRU)
noisyNetGRUSelfLoop l = coupledSelfLoop l noisyNetGRU

noisyNetGRUPeriodOne :
  ∀ (l : Law) → PeriodOne (CoupledStep l noisyNetGRU)
noisyNetGRUPeriodOne l = coupledPeriodOne l noisyNetGRU

noisyNetRecurrentProjection : RecurrentProjection
noisyNetRecurrentProjection = noisyNetProjection

noisyNetProjectionLift :
  ∀ x → RecurrentProjection.project noisyNetRecurrentProjection
    (RecurrentProjection.lift noisyNetRecurrentProjection x) ≡ x
noisyNetProjectionLift = noisyNet-project-lift

noisyNetGlobalControlPreserved :
  ∀ (s : GRUState) (x : _)
  → gruGlobalControlPersists s x
noisyNetGlobalControlPreserved s x = gruGlobalControlPersists s x
