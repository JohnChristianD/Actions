{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.TheoremRanking where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

record Rank : Set where
  constructor rank
  field
    closure identity finiteSupport extraction : Nat

noisyTriRank : Rank
noisyTriRank = rank (suc (suc (suc zero))) (suc (suc (suc zero))) (suc (suc (suc zero))) (suc (suc (suc zero)))

dmcpRank : Rank
dmcpRank = rank (suc (suc zero)) (suc (suc (suc zero))) (suc (suc zero)) (suc (suc zero))

mr15DyadicRank : Rank
mr15DyadicRank = rank (suc zero) (suc (suc zero)) (suc zero) (suc zero)

mr15DominanceOnFiniteCriteria :
  Rank.closure mr15DyadicRank +
  Rank.identity mr15DyadicRank +
  Rank.finiteSupport mr15DyadicRank +
  Rank.extraction mr15DyadicRank ≡
  suc (suc (suc (suc zero)))
mr15DominanceOnFiniteCriteria = refl

canonicalTheoremClass : Rank
canonicalTheoremClass = noisyTriRank
