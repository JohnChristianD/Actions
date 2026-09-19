{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.NovelLearnerTheoremDiscovery_test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Exotic.ERL.FullCoupled.GeneratedNovelLearnerTheorems

generatedSemanticCompositionCount-type :
  Nat
generatedSemanticCompositionCount-type =
  generatedSemanticCompositionCount

generatedSemanticCompositionCount-self :
  generatedSemanticCompositionCount ≡
  generatedSemanticCompositionCount
generatedSemanticCompositionCount-self = refl
