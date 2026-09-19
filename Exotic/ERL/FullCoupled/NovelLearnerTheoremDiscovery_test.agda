{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.NovelLearnerTheoremDiscovery_test where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith

novel-watkins-target-norm-invariance :
  ∀ K s n →
  C.canonicalWatkinsTarget K (replaceNorm s n)
  ≡
  C.canonicalWatkinsTarget K s
novel-watkins-target-norm-invariance K s n = refl

novel-watkins-target-clock-plus4-invariance :
  ∀ K s →
  C.canonicalWatkinsTarget K
    (replaceClock s
      (suc (suc (suc (suc (C.clock s))))))
  ≡
  C.canonicalWatkinsTarget K s
novel-watkins-target-clock-plus4-invariance K s = refl

novel-full-step-norm-replacement-equivariance :
  ∀ K s n →
  C.canonicalFullStep K (replaceNorm s n)
  ≡
  replaceNorm (C.canonicalFullStep K s) n
novel-full-step-norm-replacement-equivariance K s n = refl

novel-full-step-clock-plus4-equivariance :
  ∀ K s →
  C.canonicalFullStep K
    (replaceClock s
      (suc (suc (suc (suc (C.clock s))))))
  ≡
  replaceClock
    (C.canonicalFullStep K s)
    (suc (suc (suc (suc
      (C.clock (C.canonicalFullStep K s))))))
novel-full-step-clock-plus4-equivariance K s = refl
