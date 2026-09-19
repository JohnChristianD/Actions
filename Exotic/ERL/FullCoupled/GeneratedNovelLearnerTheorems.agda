{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.GeneratedNovelLearnerTheorems where

open import Agda.Builtin.Nat using (Nat)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith

-- Generated from actual executable learner/theorem declarations.
-- Reflexive declarations are excluded from the composition class.

generatedSemanticCompositionCount : Nat
generatedSemanticCompositionCount = 4

generatedSemanticComposition0 :
  ∀ K s → canonicalFullStep K s ≢ s
generatedSemanticComposition0 = C.canonicalStep-not-fixed

generatedSemanticComposition1 :
  ∀ K n s → clock (iterateCanonical K n s) ≡ clock s + n
generatedSemanticComposition1 = C.clockAfter

generatedSemanticComposition2 :
  ∀ K s n → iterateCanonical K (suc n) s ≢ s
generatedSemanticComposition2 = C.canonicalAperiodic

generatedSemanticComposition3 :
  ∀ K s → iterateCanonical K 2 s ≡ s → ⊥
generatedSemanticComposition3 = C.canonicalNoCountedTwoCycle
