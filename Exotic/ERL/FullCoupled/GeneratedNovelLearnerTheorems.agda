{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.GeneratedNovelLearnerTheorems where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith as T
open C
open T

-- Generated from actual executable learner/theorem declarations.
-- Reflexive declarations are excluded from the composition class.

generatedSemanticCompositionCount : Nat
generatedSemanticCompositionCount = 4

generatedSemanticComposition0 :
  ∀ K s → canonicalFullStep K s ≢ s
generatedSemanticComposition0 = canonicalStep-not-fixed

generatedSemanticComposition1 :
  ∀ K n s → clock (iterateCanonical K n s) ≡ clock s + n
generatedSemanticComposition1 = clockAfter

generatedSemanticComposition2 :
  ∀ K s n → iterateCanonical K (suc n) s ≢ s
generatedSemanticComposition2 = canonicalAperiodic

generatedSemanticComposition3 :
  ∀ K s → iterateCanonical K 2 s ≡ s → ⊥
generatedSemanticComposition3 = canonicalNoCountedTwoCycle
