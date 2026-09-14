{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.MR15Reachability where

open import Exotic.ERL.Exploration.DyadicLaws using
  ( Law
  ; flatDyadic
  ; mr15GA
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
  ; method-law-closure
  )

MR15State : Set
MR15State = CanonicalState

MR15Step : Law → MR15State → MR15State → Set
MR15Step flatDyadic = CoupledStep flatDyadic mr15GA

mr15IrreducibilityProof : Irreducible (MR15Step flatDyadic)
mr15IrreducibilityProof = coupledIrreducible mr15GA

mr15SelfLoopProof : SelfLoop (MR15Step flatDyadic)
mr15SelfLoopProof = coupledSelfLoop mr15GA

mr15PeriodOneProof : PeriodOne (MR15Step flatDyadic)
mr15PeriodOneProof = coupledPeriodOne mr15GA

mr15AllLawClosure : Irreducible (MR15Step flatDyadic)
mr15AllLawClosure = method-law-closure mr15GA
