{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.GeneratedNovelLearnerTheorems where

open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; trans)
open import Agda.Builtin.Nat using (suc)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith

generatedNovelLearnerTheoremBasis : NovelLearnerTheoremBasis
generatedNovelLearnerTheoremBasis = novel-learner-theorem-basis

generated_normReplacement_countStep_invariant :
  ∀ K s n →
  C.canonicalCountStep K (C.replaceNorm s n)
  ≡
  C.canonicalCountStep K s
generated_normReplacement_countStep_invariant =
  NovelLearnerTheoremBasis.normReplacementCountStep generatedNovelLearnerTheoremBasis

generated_normReplacement_qLogStep_invariant :
  ∀ K s n →
  C.canonicalQLogStep K (C.replaceNorm s n)
  ≡
  C.canonicalQLogStep K s
generated_normReplacement_qLogStep_invariant =
  NovelLearnerTheoremBasis.normReplacementQLogStep generatedNovelLearnerTheoremBasis

generated_clockPlus4_endogenousFeedback_invariant :
  ∀ K s →
  C.canonicalEndogenousFeedback K
    (replaceClock s
      (suc (suc (suc (suc (C.clock s))))))
  ≡
  C.canonicalEndogenousFeedback K s
generated_clockPlus4_endogenousFeedback_invariant =
  NovelLearnerTheoremBasis.clockPlus4EndogenousFeedback generatedNovelLearnerTheoremBasis

generated_clockPlus4_watkinsTarget_invariant :
  ∀ K s →
  C.canonicalWatkinsTarget K
    (replaceClock s
      (suc (suc (suc (suc (C.clock s))))))
  ≡
  C.canonicalWatkinsTarget K s
generated_clockPlus4_watkinsTarget_invariant =
  NovelLearnerTheoremBasis.clockPlus4WatkinsTarget generatedNovelLearnerTheoremBasis
