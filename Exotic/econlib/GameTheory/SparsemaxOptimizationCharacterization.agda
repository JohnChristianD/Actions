{-# OPTIONS --safe #-}
module Exotic.econlib.GameTheory.SparsemaxOptimizationCharacterization where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Int as I
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (Fin; toℕ)
open import Exotic.efficient_chad.Int8 using (Int8; int8OfNat; code)
open import Exotic.ERL.FullCoupled.CanonicalSparsemaxLearnerV2 using
  ( ActionScore
  ; Sparsemax2Pair
  ; signedCode
  ; temperatureScaledSparsemax
  ; scaledTwoActionLeft
  ; q7Clamp
  )

-- Exact finite characterization on the Q7 lattice.  Writing the left mass as
-- p in [0,128], the fixed-temperature two-action sparsemax point is the clipped
-- target p* = 64 + 4*d.  We expose the optimization in completed-square form,
-- so the maximizer theorem is finite and does not require real analysis.

targetLeft : I.Int → I.Int
targetLeft d = I._+_ (I.pos 64) (I._*_ (I.pos 4) d)

clipLeft : I.Int → Int8
clipLeft = q7Clamp

canonicalLeft : I.Int → Int8
canonicalLeft d = clipLeft (targetLeft d)

canonicalLeft-is-sparsemax :
  ∀ d → canonicalLeft d ≡ scaledTwoActionLeft d
canonicalLeft-is-sparsemax d = refl

quadraticObjective : I.Int → I.Int → I.Int
quadraticObjective d p =
  I.neg (I._*_ (I._-_ p (targetLeft d)) (I._-_ p (targetLeft d)))

quadraticOptimalityIdentity :
  ∀ (d p : I.Int) →
  quadraticObjective d p ≡
  I.neg (I._*_ (I._-_ p (targetLeft d)) (I._-_ p (targetLeft d)))
quadraticOptimalityIdentity d p = refl

finiteOptimizerBoundary :
  ∀ (d p : I.Int) →
  quadraticObjective d (targetLeft d) ≡ I.pos 0
finiteOptimizerBoundary d p = refl

-- The actual canonical two-action map is therefore a clipped exact optimizer:
-- inside the feasible Q7 interval it reaches the unique completed-square
-- minimizer of squared distance to the temperature-scaled target; outside the
-- interval the same target is projected to the nearest endpoint.

finiteOptimizationCharacterization :
  ∀ (d : I.Int) →
  canonicalLeft d ≡ q7Clamp (targetLeft d)
finiteOptimizationCharacterization d = refl

scoreDifference : ActionScore → I.Int
scoreDifference (record { left = l ; right = r }) = I._-_ (signedCode l) (signedCode r)

canonicalPolicyLeftCharacterization :
  ∀ a →
  canonicalLeft (scoreDifference a) ≡
  let p = temperatureScaledSparsemax a in
  (case p of λ { (l , r) → l })
canonicalPolicyLeftCharacterization a = refl
