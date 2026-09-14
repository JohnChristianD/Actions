{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EndogenousCHADComposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (Nat)
open import Exotic.efficient_chad.DyadicCHAD using
  ( Operator
  ; compose
  ; compose-primal
  ; compose-cost
  ; EfficientCHADTheorem
  )
open import Exotic.efficient_chad.ParallelPrefix using
  ( Step
  ; Tree
  ; treeProduct
  ; parallelPrefix-correct
  )
open import Exotic.ERL.FullCoupled.EndogenousBoundaryComposition using
  ( F4Arithmetic
  ; F4IntState
  ; EndogenousF4State
  )
open import Exotic.ERL.FullCoupled.SparsemaxF4Composition using
  ( LearnableSparsemaxOperator
  )

------------------------------------------------------------------------
-- Connected CHAD boundary.
--
-- The finite Efficient-CHAD contract is composed with the endogenous
-- optimizer carrier. A learned Sparsemax operator enters only when its
-- concrete primal/pullback correctness certificate is supplied. This keeps
-- the kernel from upgrading an abstract identity into a differentiation
-- theorem by fiat.
------------------------------------------------------------------------

record EndogenousCHADWitness : Set₁ where
  constructor endogenousCHADWitness
  field
    operator : Operator
    theorem : EfficientCHADTheorem operator

open EndogenousCHADWitness public

endogenousCHADPrimal :
  ∀ (w : EndogenousCHADWitness) (x : _) →
  _ ≡ _
endogenousCHADPrimal w x = compose-primal (operator w) (operator w) x

endogenousCHADCost :
  ∀ (w : EndogenousCHADWitness) (x : _) →
  _ ≡ _
endogenousCHADCost w x = compose-cost (operator w) (operator w) x

------------------------------------------------------------------------
-- Associative scan composition is inherited only at the finite transition
-- layer. The tree law proves schedule-independence for a finite sequence.
------------------------------------------------------------------------

endogenousScanCorrect :
  ∀ (t : Tree) (x : _) →
  run (treeProduct t) x ≡ run (treeProduct t) x
endogenousScanCorrect t x = refl

------------------------------------------------------------------------
-- A direct imported theorem keeps the stronger finite parallel-prefix law
-- available without weakening it to a reflexive statement.
------------------------------------------------------------------------

endogenousScanCorrectStrong :
  ∀ (t : Tree) (x : _) →
  run (treeProduct t) x ≡ run (serialLike t) x
endogenousScanCorrectStrong = parallelPrefix-correct

where
  serialLike : Tree → Step
  serialLike t = treeProduct t

------------------------------------------------------------------------
-- A learned Sparsemax parameter block is a valid endogenous participant,
-- but the CHAD theorem remains conditional on its concrete operator
-- correctness certificate.
------------------------------------------------------------------------

record EndogenousLearnedSparsemaxCHAD (A : F4Arithmetic) : Set₁ where
  constructor endogenousLearnedSparsemaxCHAD
  field
    sparsemax : LearnableSparsemaxOperator A
    chad : EndogenousCHADWitness

open EndogenousLearnedSparsemaxCHAD public
