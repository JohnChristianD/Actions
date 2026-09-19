{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.GeneratedNovelLearnerTheorems where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith as T
open C
open T

-- Generated from the shared semantic manifest and its e-graph quotient.
-- These declarations are projections of source-owned theorem declarations.

generatedSemanticDerivedCount : Nat
generatedSemanticDerivedCount = 4

generatedSemanticEGraphQuotientCount : Nat
generatedSemanticEGraphQuotientCount = 4

generatedSemanticDerived0 :
  ∀ K s → canonicalFullStep K s ≢ s
generatedSemanticDerived0 = T.canonicalStep-not-fixed

generatedSemanticDerived1 :
  ∀ K n s → clock (iterateCanonical K n s) ≡ clock s + n
generatedSemanticDerived1 = T.clockAfter

generatedSemanticDerived2 :
  ∀ K s n → iterateCanonical K (suc n) s ≢ s
generatedSemanticDerived2 = T.canonicalAperiodic

generatedSemanticDerived3 :
  ∀ K s → iterateCanonical K 2 s ≡ s → ⊥
generatedSemanticDerived3 = T.canonicalNoCountedTwoCycle
