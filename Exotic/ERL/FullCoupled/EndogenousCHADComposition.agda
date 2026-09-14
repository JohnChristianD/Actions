{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EndogenousCHADComposition where

open import Agda.Builtin.Equality using (_≡_)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.efficient_chad.DyadicCHAD using
  ( Operator
  ; source
  ; primal
  ; cost
  ; compose
  ; compose-primal
  ; compose-cost
  ; PreservesPrimal
  ; EfficientCHADTheorem
  )
open import Exotic.efficient_chad.ParallelPrefix using
  ( Step
  ; run
  ; Tree
  ; flatten
  ; serial
  ; treeProduct
  ; parallelPrefix-correct
  )
open import Exotic.ERL.FullCoupled.EndogenousBoundaryComposition using
  ( F4Arithmetic
  )
open import Exotic.ERL.FullCoupled.SparsemaxF4Composition using
  ( LearnableSparsemaxOperator
  )

------------------------------------------------------------------------
-- Connected CHAD boundary.
--
-- CHAD/Efficient-CHAD theorems are part of the endogenous learner only when
-- the operator carries an explicit primal/pullback correctness certificate.
-- The kernel never upgrades a bare implementation identity into a derivative
-- correctness claim.
------------------------------------------------------------------------

record EndogenousCHADWitness : Set₁ where
  constructor endogenousCHADWitness
  field
    operator : Operator
    theorem : EfficientCHADTheorem operator

open EndogenousCHADWitness public

endogenousCHADPrimal :
  ∀ (w : EndogenousCHADWitness) (x : Int8) →
  primal (operator w) x ≡ source (operator w) x
endogenousCHADPrimal w x =
  PreservesPrimal.theorem
    (EfficientCHADTheorem.primal-preserved (theorem w)) x

endogenousCHADCompositePrimal :
  ∀ (w : EndogenousCHADWitness) (x : Int8) →
  primal (compose (operator w) (operator w)) x
  ≡ source (compose (operator w) (operator w)) x
endogenousCHADCompositePrimal w x =
  compose-primal (operator w) (operator w) x

endogenousCHADCompositeCost :
  ∀ (w : EndogenousCHADWitness) (x : Int8) →
  cost (compose (operator w) (operator w)) x
  ≡ cost (operator w) (primal (operator w) x) + cost (operator w) x
endogenousCHADCompositeCost w x =
  compose-cost (operator w) (operator w) x

------------------------------------------------------------------------
-- Efficient endogenous scan theorem: the same finite transition sequence is
-- independent of the chosen binary reduction tree.
------------------------------------------------------------------------

endogenousParallelPrefix :
  ∀ (t : Tree) (x : Int8) →
  run (treeProduct t) x ≡ run (serial (flatten t)) x
endogenousParallelPrefix = parallelPrefix-correct

------------------------------------------------------------------------
-- Learned Sparsemax is a stronger parameterized participant, but its CHAD
-- status remains conditional on a concrete finite operator certificate.
------------------------------------------------------------------------

record EndogenousLearnedSparsemaxCHAD (A : F4Arithmetic) : Set₁ where
  constructor endogenousLearnedSparsemaxCHAD
  field
    sparsemax : LearnableSparsemaxOperator A
    chad : EndogenousCHADWitness

open EndogenousLearnedSparsemaxCHAD public
