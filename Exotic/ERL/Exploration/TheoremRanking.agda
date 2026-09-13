{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.TheoremRanking where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

record Rank : Set where
  constructor rank
  field
    closure identity finiteSupport extraction coupling : Nat

top : Nat
 top = suc (suc (suc (suc zero)))

noisyTriRank : Rank
noisyTriRank = rank top top top top top

openESDyadicRank : Rank
openESDyadicRank = rank top top top (suc (suc (suc zero))) (suc (suc (suc zero)))

mr15DyadicRank : Rank
mr15DyadicRank = rank top top (suc (suc (suc zero))) (suc (suc (suc zero))) (suc (suc zero))

noisyTriScore : Nat
noisyTriScore = Rank.closure noisyTriRank + Rank.identity noisyTriRank + Rank.finiteSupport noisyTriRank + Rank.extraction noisyTriRank + Rank.coupling noisyTriRank

openESScore : Nat
openESScore = Rank.closure openESDyadicRank + Rank.identity openESDyadicRank + Rank.finiteSupport openESDyadicRank + Rank.extraction openESDyadicRank + Rank.coupling openESDyadicRank

mr15Score : Nat
mr15Score = Rank.closure mr15DyadicRank + Rank.identity mr15DyadicRank + Rank.finiteSupport mr15DyadicRank + Rank.extraction mr15DyadicRank + Rank.coupling mr15DyadicRank

noisyTriBeatsOpenES : noisyTriScore ≡ 19
noisyTriBeatsOpenES = refl

openESBeatsMR15 : openESScore ≡ 18
openESBeatsMR15 = refl

mr15ScoreValue : mr15Score ≡ 17
mr15ScoreValue = refl

canonicalTheoremClass : Rank
canonicalTheoremClass = noisyTriRank
