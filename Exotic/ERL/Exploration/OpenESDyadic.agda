{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.OpenESDyadic where

open import Exotic.ERL.Exploration.DyadicLaws using
  ( Law
  ; Method
  ; flatDyadic
  ; lazyUnit
  ; dyadicLadder
  ; openES
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
  )

OpenESState : Set
OpenESState = CoupledState

openESStep : Law → OpenESState → OpenESState → Set
openESStep l = CoupledStep l openES

openESIrreducibilityProof :
  ∀ (l : Law) → Irreducible (openESStep l)
openESIrreducibilityProof l = coupledIrreducible l openES

openESSelfLoopProof :
  ∀ (l : Law) → SelfLoop (openESStep l)
openESSelfLoopProof l = coupledSelfLoop l openES

openESPeriodOneProof :
  ∀ (l : Law) → PeriodOne (openESStep l)
openESPeriodOneProof l = coupledPeriodOne l openES
