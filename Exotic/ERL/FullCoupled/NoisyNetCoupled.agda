{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.NoisyNetCoupled where

open import Agda.Builtin.Equality using (_≡_)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.Exploration.DyadicLaws using
  ( Law
  ; flatDyadic
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
  Irreducible (CoupledStep flatDyadic noisyNetGRU)
noisyNetGRUIrreducible = coupledIrreducible noisyNetGRU

noisyNetGRUSelfLoop :
  SelfLoop (CoupledStep flatDyadic noisyNetGRU)
noisyNetGRUSelfLoop = coupledSelfLoop noisyNetGRU

noisyNetGRUPeriodOne :
  PeriodOne (CoupledStep flatDyadic noisyNetGRU)
noisyNetGRUPeriodOne = coupledPeriodOne noisyNetGRU

noisyNetRecurrentProjection : RecurrentProjection
noisyNetRecurrentProjection = noisyNetProjection

noisyNetProjectionLift :
  ∀ x → RecurrentProjection.project noisyNetRecurrentProjection
    (RecurrentProjection.lift noisyNetRecurrentProjection x) ≡ x
noisyNetProjectionLift = noisyNet-project-lift

noisyNetGlobalControlPreserved :
  ∀ (s : GRUState) (x : Int8) →
  gruStep s x |>.global ≡ GRUState.global s
noisyNetGlobalControlPreserved s x = gruGlobalControlPersists s x
