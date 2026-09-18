{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.LearnerComposition_Discovery_test where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List.Base using ([])
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith

policy-attention-norm-optimizer-composition :
  ∀ K s a n o →
  C.canonicalPolicy K
    (applyLearnerReplacements
      (attentionReplacement a ∷
       normReplacement n ∷
       optimizerReplacement o ∷ [])
      s)
  ≡
  C.canonicalPolicy K s
policy-attention-norm-optimizer-composition K s a n o =
  canonicalPolicy-learnerReplacement-composition
    K
    s
    (attentionReplacement a ∷
     normReplacement n ∷
     optimizerReplacement o ∷ [])

policy-optimizer-attention-composition :
  ∀ K s a o →
  C.canonicalPolicy K
    (applyLearnerReplacements
      (optimizerReplacement o ∷
       attentionReplacement a ∷ [])
      s)
  ≡
  C.canonicalPolicy K s
policy-optimizer-attention-composition K s a o =
  canonicalPolicy-learnerReplacement-composition
    K
    s
    (optimizerReplacement o ∷
     attentionReplacement a ∷ [])

norm-preservation-composition-3 :
  ∀ K s →
  C.normPairWeightPlusOne
    (C.norm (C.iterateCanonical K 3 s))
  ≡
  C.normPairWeightPlusOne (C.norm s)
norm-preservation-composition-3 K s =
  canonicalNormPair-afterFullStep-iterate K 3 s

persistent-gru-composition-3 :
  ∀ K s →
  C.persistentGRU
    (C.gru (C.iterateCanonical K 3 s))
  ≡
  C.persistentGRU (C.gru s)
persistent-gru-composition-3 K s =
  canonicalPersistentGRU-afterFullStep-iterate K 3 s
