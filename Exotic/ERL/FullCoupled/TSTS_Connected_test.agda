{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TSTS_Connected_test where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith

tsts-selected-target-test :
  ∀ K p d s →
  finiteTSTSSelectedTarget K p d s
  ≡
  C.canonicalWatkinsTarget K
    (finiteTSTSSelectedProbe K p d s)
tsts-selected-target-test =
  FiniteTSTSEndogenousConnectedTheorem.selectedTarget-law
    finite-tsts-endogenous-connected-theorem

tsts-selected-posterior-update-test :
  ∀ K p d s →
  finiteTSTSBranchSample
    (finiteTSTSNextPosterior K p d s)
    (finiteTSTSSelectedBranch p)
  ≡
  finiteTSTSBranchSample p (finiteTSTSSelectedBranch p)
  + finiteTSTSReward K p d s
tsts-selected-posterior-update-test =
  FiniteTSTSEndogenousConnectedTheorem.posteriorUpdateUsesEndogenousReward
    finite-tsts-endogenous-connected-theorem

tsts-selected-gru-feed-test :
  ∀ K p d s →
  C.canonicalGRUStep K (finiteTSTSSelectedProbe K p d s)
  ≡
  C.gruStep
    (C.gru s)
    (C.int8Add
      (finiteTSTSSelectedTarget K p d s)
      (C.canonicalAttentionMix K s))
tsts-selected-gru-feed-test =
  FiniteTSTSEndogenousConnectedTheorem.selectedTargetFeedsGRU
    finite-tsts-endogenous-connected-theorem

tsts-selected-f4-feed-test :
  ∀ K p d s →
  C.canonicalOptimizerStep K (finiteTSTSSelectedProbe K p d s)
  ≡
  C.f4ThetaStep
    (C.optimizerKernel K)
    (C.optimizer (finiteTSTSSelectedProbe K p d s))
    (finiteTSTSSelectedTarget K p d s)
tsts-selected-f4-feed-test =
  FiniteTSTSEndogenousConnectedTheorem.selectedTargetFeedsF4
    finite-tsts-endogenous-connected-theorem

tsts-f4-endogenous-expansion-test :
  ∀ K p d s →
  finiteTSTSSelectedBranch p ≡ tstsF4L2Branch →
  finiteTSTSSelectedTarget K p d s
  ≡
  C.int8Add
    (C.int8Add
      (C.int8Add
        (C.canonicalReward8 K s)
        (C.canonicalQLogBias K s))
      (C.int8Mul
        C.canonicalDiscount8
        (C.maxCriticValue8 (C.critic (C.watkins s)))))
    (C.int8Add
      (C.canonicalAttentionMix K s)
      (C.int8Add
        (C.canonicalGRUFeedback s)
        (C.int8Add
          (C.int8Add
            (C.int8Add
              (C.thetaQ (C.optimizer s))
              d)
            (C.l2Correction (C.globalL2 (C.optimizerKernel K))))
          (C.int8Add
            (C.canonicalQLogControlFeedback s)
            (C.canonicalQLogValueFeedback s))))
tsts-f4-endogenous-expansion-test =
  FiniteTSTSEndogenousConnectedTheorem.f4SelectedEndogenousExpansion
    finite-tsts-endogenous-connected-theorem

tsts-selected-invariants-test :
  ∀ K p d s →
  C.normPairWeightPlusOne
    (C.norm (finiteTSTSClosedStep K p d s))
  ≡
  C.normPairWeightPlusOne (C.norm s)
tsts-selected-invariants-test =
  FiniteTSTSEndogenousConnectedTheorem.normPairPreserved
    finite-tsts-endogenous-connected-theorem

tsts-selected-persistent-gru-test :
  ∀ K p d s →
  C.persistentGRU
    (C.gru (finiteTSTSClosedStep K p d s))
  ≡
  C.persistentGRU
    (C.gru (finiteTSTSSelectedProbe K p d s))
tsts-selected-persistent-gru-test =
  FiniteTSTSEndogenousConnectedTheorem.persistentGRUPreserved
    finite-tsts-endogenous-connected-theorem
