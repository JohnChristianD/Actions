{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.NovelLearnerTheoremDiscovery_test where

open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; trans)
open import Agda.Builtin.Nat using (suc)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith

candidate_normReplacement_countStep_invariant :
  ∀ K s n →
  C.canonicalCountStep K (C.replaceNorm s n)
  ≡
  C.canonicalCountStep K s
candidate_normReplacement_countStep_invariant K s n =
  cong₂ C.updateLCBCount
    (canonicalPolicy-norm-invariant K s n)
    refl

candidate_normReplacement_qLogStep_invariant :
  ∀ K s n →
  C.canonicalQLogStep K (C.replaceNorm s n)
  ≡
  C.canonicalQLogStep K s
candidate_normReplacement_qLogStep_invariant K s n =
  cong
    (λ p → C.negativeFiniteQLog8 (C.policyLeftWeight p))
    (canonicalPolicy-norm-invariant K s n)

candidate_clockPlus4_endogenousFeedback_invariant :
  ∀ K s →
  C.canonicalEndogenousFeedback K
    (replaceClock s
      (suc (suc (suc (suc (C.clock s))))))
  ≡
  C.canonicalEndogenousFeedback K s
candidate_clockPlus4_endogenousFeedback_invariant K s =
  cong
    (λ x →
      C.int8Add
        x
        (C.int8Add
          (C.canonicalGRUFeedback s)
          (C.int8Add
            (C.canonicalF4L2Feedback K s)
            (C.int8Add
              (C.canonicalQLogControlFeedback s)
              (C.canonicalQLogValueFeedback s)))))
    (canonicalAttentionMix-clock-period4 K s)

candidate_clockPlus4_watkinsTarget_invariant :
  ∀ K s →
  C.canonicalWatkinsTarget K
    (replaceClock s
      (suc (suc (suc (suc (C.clock s))))))
  ≡
  C.canonicalWatkinsTarget K s
candidate_clockPlus4_watkinsTarget_invariant K s =
  trans
    (C.canonicalWatkinsTarget-law K
      (replaceClock s
        (suc (suc (suc (suc (C.clock s)))))))
    (cong
      (λ x →
        C.int8Add
          (C.int8Add
            (C.int8Add
              (C.canonicalReward8 K s)
              (C.canonicalQLogBias K s))
            (C.int8Mul
              C.canonicalDiscount8
              (C.maxCriticValue8 (C.critic (C.watkins s)))))
          x)
      candidate_clockPlus4_endogenousFeedback_invariant K s)
