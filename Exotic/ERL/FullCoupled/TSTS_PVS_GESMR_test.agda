{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TSTS_PVS_GESMR_test where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith

tsts-pvs-f4-probe-test :
  ∀ d s →
  finiteTSTSSelectedProbe d s
  ≡
  finiteGESMRProbe gesmrF4L2Group d s
tsts-pvs-f4-probe-test =
  FiniteTSTSPVSGESMRConnectedTheorem.selectedProbeIsF4L2Probe
    finite-tsts-pvs-gesmr-connected-theorem

tsts-pvs-watkins-chain-test :
  ∀ K s d →
  C.canonicalWatkinsTarget K (finiteTSTSSelectedProbe d s)
  ≡
  C.canonicalWatkinsTarget K
    (finiteGESMRProbe gesmrF4L2Group d s)
tsts-pvs-watkins-chain-test =
  FiniteTSTSPVSGESMRConnectedTheorem.endogenousWatkinsAfterSelection
    finite-tsts-pvs-gesmr-connected-theorem

tsts-pvs-no-second-optimizer-test :
  ∀ K s d →
  finitePVSPVRecheck K s d
  ≡
  C.canonicalFullStep
    K
    (finiteGESMRProbe gesmrF4L2Group d s)
tsts-pvs-no-second-optimizer-test =
  FiniteTSTSPVSGESMRConnectedTheorem.noSecondOptimizerModel
    finite-tsts-pvs-gesmr-connected-theorem

tsts-pvs-norm-preservation-test :
  ∀ K s d →
  C.normPairWeightPlusOne
    (C.norm (finitePVSPVRecheck K s d))
  ≡
  C.normPairWeightPlusOne (C.norm s)
tsts-pvs-norm-preservation-test =
  FiniteTSTSPVSGESMRConnectedTheorem.normPairPreservedAfterSelection
    finite-tsts-pvs-gesmr-connected-theorem

tsts-pvs-persistent-gru-test :
  ∀ K s d →
  C.persistentGRU
    (C.gru (finitePVSPVRecheck K s d))
  ≡
  C.persistentGRU
    (C.gru (finiteTSTSSelectedProbe d s))
tsts-pvs-persistent-gru-test =
  FiniteTSTSPVSGESMRConnectedTheorem.persistentGRUPreservedAfterSelection
    finite-tsts-pvs-gesmr-connected-theorem

tsts-pvs-end-to-end-closed-loop-test :
  ∀ K s d →
  finitePVSPVRecheck K s d
  ≡
  C.canonicalFullStep K (finiteTSTSSelectedProbe d s)
tsts-pvs-end-to-end-closed-loop-test =
  FiniteTSTSPVSGESMRConnectedTheorem.tstsPvsEndogenousClosedLoop
    finite-tsts-pvs-gesmr-connected-theorem

tsts-pvs-f4-watkins-gru-chain-test :
  ∀ K s d →
  C.canonicalGRUStep K (finiteTSTSSelectedProbe d s)
  ≡
  C.gruStep
    (C.gru s)
    (C.int8Add
      (C.canonicalWatkinsTarget K (finiteTSTSSelectedProbe d s))
      (C.canonicalAttentionMix K s))
tsts-pvs-f4-watkins-gru-chain-test =
  FiniteTSTSPVSGESMRConnectedTheorem.tstsPvsF4WatkinsGRUChain
    finite-tsts-pvs-gesmr-connected-theorem
