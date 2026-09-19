{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.NovelLearnerTheoremDiscovery_test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Exotic.ERL.FullCoupled.GeneratedNovelLearnerTheorems

generatedSemanticDerivedCount-type :
  Nat
generatedSemanticDerivedCount-type =
  generatedSemanticDerivedCount

generatedSemanticDerivedCount-self :
  generatedSemanticDerivedCount ≡
  generatedSemanticDerivedCount
generatedSemanticDerivedCount-self = refl
