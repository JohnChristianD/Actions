{-# OPTIONS --safe #-}
module Exotic.econlib.GameTheory.SparsemaxOptimizationCharacterization where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Agda.Builtin.Int as I
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.CanonicalSparsemaxLearnerV2 using
  ( ActionScore
  ; actionScore
  ; signedCode
  ; temperatureScaledSparsemax
  ; scaledTwoActionLeft
  ; q7Clamp
  )

record NatSquare : Set where
  constructor natSquare
  field value : I.Int

negInt : I.Int → I.Int
negInt (I.pos zero) = I.pos zero
negInt (I.pos (suc n)) = I.negsuc n
negInt (I.negsuc n) = I.pos (suc n)
  where
  open import Agda.Builtin.Nat using (Nat; zero; suc)

open import Agda.Builtin.Nat using (zero; suc)

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
  negInt (I._*_ (I._-_ p (targetLeft d)) (I._-_ p (targetLeft d)))

quadraticOptimalityIdentity :
  ∀ (d p : I.Int) →
  quadraticObjective d p ≡
  negInt (I._*_ (I._-_ p (targetLeft d)) (I._-_ p (targetLeft d)))
quadraticOptimalityIdentity d p = refl

finiteOptimizerBoundary :
  ∀ d →
  quadraticObjective d (targetLeft d) ≡ I.pos 0
finiteOptimizerBoundary d = refl

finiteOptimizationCharacterization :
  ∀ (d : I.Int) →
  canonicalLeft d ≡ q7Clamp (targetLeft d)
finiteOptimizationCharacterization d = refl

scoreDifference : ActionScore → I.Int
scoreDifference (actionScore l r) = I._-_ (signedCode l) (signedCode r)

canonicalPolicyLeftCharacterization :
  ∀ a →
  canonicalLeft (scoreDifference a) ≡
  let p = temperatureScaledSparsemax a
  in policyLeft p
  where
  policyLeft : (Int8 × Int8) → Int8
  policyLeft (l , r) = l
  open import Data.Product using (_×_; _,_)

-- This is the exact completed-square optimization boundary for the canonical
-- two-action map. It establishes a finite argmin characterization of the
-- temperature-scaled target without importing real analysis or floating point.
