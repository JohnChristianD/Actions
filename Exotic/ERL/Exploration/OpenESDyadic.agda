{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.OpenESDyadic where

open import Exotic.ERL.Exploration.DyadicLaws using
  ( Law
  ; Method
  ; flatDyadic
  ; openES
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

openESIrreducibilityProof : Irreducible (openESStep flatDyadic)
openESIrreducibilityProof = coupledIrreducible openES

openESSelfLoopProof : SelfLoop (openESStep flatDyadic)
openESSelfLoopProof = coupledSelfLoop openES

openESPeriodOneProof : PeriodOne (openESStep flatDyadic)
openESPeriodOneProof = coupledPeriodOne openES
