{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.OpenESDyadic where

open import Exotic.ERL.Exploration.DyadicLaws using
  ( Law
  ; flatDyadic
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Irreducible
  ; SelfLoop
  ; PeriodOne
  )
open import Exotic.ERL.FullCoupled.DyadicMethodLawCoupling using
  ( CanonicalState
  ; CoupledStep
  ; coupledIrreducible
  ; coupledSelfLoop
  ; coupledPeriodOne
  )

OpenESState : Set
OpenESState = CanonicalState

openESStep : Law → OpenESState → OpenESState → Set
openESStep flatDyadic = CoupledStep flatDyadic openES
  where
  openES = record {}

openESIrreducibilityProof : Irreducible (openESStep flatDyadic)
openESIrreducibilityProof = coupledIrreducible openES
  where
  openES = record {}

openESSelfLoopProof : SelfLoop (openESStep flatDyadic)
openESSelfLoopProof = coupledSelfLoop openES
  where
  openES = record {}

openESPeriodOneProof : PeriodOne (openESStep flatDyadic)
openESPeriodOneProof = coupledPeriodOne openES
  where
  openES = record {}
