{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.GeneratedNovelLearnerTheorems where

open import Agda.Builtin.Nat using (Nat)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith as T
open C
open T

-- Generated from the source-derived semantic manifest and Mercury e-graph.
generatedSemanticDerivedCount : Nat
generatedSemanticDerivedCount = 5

generatedSemanticEGraphQuotientCount : Nat
generatedSemanticEGraphQuotientCount = 5

generatedCanonicalEndogenousMinimaxBellmanShapleyUAP :
  T.CanonicalEndogenousMinimaxBellmanShapleyUAPTheorem
generatedCanonicalEndogenousMinimaxBellmanShapleyUAP =
  T.canonical-endogenous-minimax-bellman-shapley-uap-theorem

generatedSemanticDerived0 =
  T.canonicalStep-not-fixed

generatedSemanticDerived1 =
  T.clockAfter

generatedSemanticDerived2 =
  T.canonicalAperiodic

generatedSemanticDerived3 =
  T.canonicalNoCountedTwoCycle
