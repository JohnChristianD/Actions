{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.LearnerComposition_Discovery_test where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List.Base using ([])
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith

policy-attention-norm-optimizer-composition :
  ∀ K s a n o →
  C.canonicalPolicy K
    (C.applyLearnerReplacements
      (C.attentionReplacement a ∷
       C.normReplacement n ∷
       C.optimizerReplacement o ∷ [])
      s)
  ≡
  C.canonicalPolicy K s
policy-attention-norm-optimizer-composition K s a n o =
  C.canonicalPolicy-learnerReplacement-composition
    K
    s
    (C.attentionReplacement a ∷
     C.normReplacement n ∷
     C.optimizerReplacement o ∷ [])

policy-optimizer-attention-composition :
  ∀ K s a o →
  C.canonicalPolicy K
    (C.applyLearnerReplacements
      (C.optimizerReplacement o ∷
       C.attentionReplacement a ∷ [])
      s)
  ≡
  C.canonicalPolicy K s
policy-optimizer-attention-composition K s a o =
  C.canonicalPolicy-learnerReplacement-composition
    K
    s
    (C.optimizerReplacement o ∷
     C.attentionReplacement a ∷ [])

norm-preservation-composition-3 :
  ∀ K s →
  C.normPairWeightPlusOne
    (C.norm (C.iterateCanonical K 3 s))
  ≡
  C.normPairWeightPlusOne (C.norm s)
norm-preservation-composition-3 K s =
  C.canonicalNormPair-afterFullStep-iterate K 3 s

persistent-gru-composition-3 :
  ∀ K s →
  C.persistentGRU
    (C.gru (C.iterateCanonical K 3 s))
  ≡
  C.persistentGRU (C.gru s)
persistent-gru-composition-3 K s =
  C.canonicalPersistentGRU-afterFullStep-iterate K 3 s
