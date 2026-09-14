{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.MR15Reachability where

open import Exotic.ERL.Exploration.DyadicLaws using
  ( Law
  ; Method
  ; flatDyadic
  ; lazyUnit
  ; dyadicLadder
  ; mr15GA
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Irreducible
  ; SelfLoop
  ; PeriodOne
  )
open import Exotic.ERL.FullCoupled.DyadicMethodLawCoupling using
  ( CoupledState
  ; CoupledStep
  ; coupledIrreducible
  ; coupledSelfLoop
  ; coupledPeriodOne
  ; method-law-closure
  )

MR15State : Set
MR15State = CoupledState

MR15Step : Law → MR15State → MR15State → Set
MR15Step l = CoupledStep l mr15GA

mr15IrreducibilityProof :
  ∀ (l : Law) → Irreducible (MR15Step l)
mr15IrreducibilityProof l = coupledIrreducible l mr15GA

mr15SelfLoopProof :
  ∀ (l : Law) → SelfLoop (MR15Step l)
mr15SelfLoopProof l = coupledSelfLoop l mr15GA

mr15PeriodOneProof :
  ∀ (l : Law) → PeriodOne (MR15Step l)
mr15PeriodOneProof l = coupledPeriodOne l mr15GA

mr15AllLawClosure :
  ∀ (l : Law) → Irreducible (MR15Step l)
mr15AllLawClosure = mr15IrreducibilityProof
