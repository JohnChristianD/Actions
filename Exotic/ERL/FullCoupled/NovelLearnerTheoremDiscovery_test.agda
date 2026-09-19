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

novelBasis-associativeScan :
  RecurrentAssociativeScanTheorem C.GRUState C.Int8
novelBasis-associativeScan =
  canonicalGRU-recurrent-associative-scan-theorem

novelBasis-prefixSplit :
  ∀ (xs : Nat → C.Int8) (m n : Nat) (s : C.GRUState) →
  C.recurrentPrefixState
    C.canonicalGRURecurrentNetwork
    xs
    (m + n)
    s
  ≡
  C.recurrentPrefixState
    C.canonicalGRURecurrentNetwork
    (C.shiftInput xs m)
    n
    (C.recurrentPrefixState
      C.canonicalGRURecurrentNetwork
      xs
      m
      s)
novelBasis-prefixSplit =
  C.canonicalGRU-recurrent-prefix-split
