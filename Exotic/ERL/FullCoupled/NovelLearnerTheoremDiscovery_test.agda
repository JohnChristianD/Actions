{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.NovelLearnerTheoremDiscovery_test where

open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith
open import Exotic.ERL.FullCoupled.GeneratedNovelLearnerTheorems

novelBasis-roundtrip :
  NovelLearnerTheoremBasis
novelBasis-roundtrip = generatedNovelLearnerTheoremBasis

novelBasis-recurrentNetwork :
  ∀ (s : C.GRUState) (x : C.Int8) →
  C.runNetwork C.canonicalGRURecurrentNetwork s x
  ≡
  C.gruStep s x
novelBasis-recurrentNetwork = C.canonicalGRUNetwork-law
