{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.NovelLearnerTheoremDiscovery_test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith
open import Exotic.ERL.FullCoupled.GeneratedNovelLearnerTheorems

novelBasis-roundtrip :
  NovelLearnerTheoremBasis
novelBasis-roundtrip = generatedNovelLearnerTheoremBasis

novelBasis-countStep :
  ∀ K s n →
  C.canonicalCountStep K (C.replaceNorm s n)
  ≡
  C.canonicalCountStep K s
novelBasis-countStep =
  NovelLearnerTheoremBasis.normReplacementCountStep novelBasis-roundtrip

novelBasis-qLogStep :
  ∀ K s n →
  C.canonicalQLogStep K (C.replaceNorm s n)
  ≡
  C.canonicalQLogStep K s
novelBasis-qLogStep =
  NovelLearnerTheoremBasis.normReplacementQLogStep novelBasis-roundtrip

novelBasis-recurrentNetwork :
  ∀ (s : C.GRUState) (x : C.Int8) →
  C.runNetwork C.canonicalGRURecurrentNetwork s x
  ≡
  C.gruStep s x
novelBasis-recurrentNetwork = C.canonicalGRUNetwork-law
