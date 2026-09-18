{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TSTS_Connected_test where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith

tsts-selected-target-test :
  ∀ K s d →
  finiteTSTSSelectedTarget K s d
  ≡
  C.canonicalWatkinsTarget K
    (finiteTSTSSelectedProbe K s d)
tsts-selected-target-test =
  finiteTSTSSelectedTarget-law

tsts-selected-gru-feed-test :
  ∀ K s d →
  C.canonicalGRUStep K (finiteTSTSSelectedProbe K s d)
  ≡
  C.gruStep
    (C.gru s)
    (C.int8Add
      (finiteTSTSSelectedTarget K s d)
      (C.canonicalAttentionMix K s))
tsts-selected-gru-feed-test =
  FiniteTSTSEndogenousConnectedTheorem.selectedTargetFeedsGRU
    finite-tsts-endogenous-connected-theorem

tsts-selected-f4-feed-test :
  ∀ K s d →
  C.canonicalOptimizerStep K (finiteTSTSSelectedProbe K s d)
  ≡
  C.f4ThetaStep
    (C.optimizerKernel K)
    (finiteTSTSSelectedF4State K s d)
    (finiteTSTSSelectedTarget K s d)
tsts-selected-f4-feed-test =
  FiniteTSTSEndogenousConnectedTheorem.selectedTargetFeedsF4
    finite-tsts-endogenous-connected-theorem

tsts-selected-invariants-test :
  ∀ K s d →
  C.normPairWeightPlusOne
    (C.norm (finiteTSTSClosedStep K s d))
  ≡
  C.normPairWeightPlusOne (C.norm s)
tsts-selected-invariants-test =
  FiniteTSTSEndogenousConnectedTheorem.normPairPreserved
    finite-tsts-endogenous-connected-theorem

tsts-selected-persistent-gru-test :
  ∀ K s d →
  C.persistentGRU
    (C.gru (finiteTSTSClosedStep K s d))
  ≡
  C.persistentGRU
    (C.gru (finiteTSTSSelectedProbe K s d))
tsts-selected-persistent-gru-test =
  FiniteTSTSEndogenousConnectedTheorem.persistentGRUPreserved
    finite-tsts-endogenous-connected-theorem
