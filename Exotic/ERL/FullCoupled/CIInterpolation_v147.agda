{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CIInterpolation_v147 where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Exotic.ERL.FullCoupled.CompleteSafe_v147
open import Exotic.ERL.FullCoupled.QClosure_v147

------------------------------------------------------------------------
-- CI surface: names are thin aliases to kernel-checkable constructive proofs.
------------------------------------------------------------------------

qNumRemove_v147 : ∀ {S} (n y : Scalar S) →
  (n + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) y) + y ≡ n
qNumRemove_v147 = qNumRemove_v147

qDenRemove_v147 : ∀ {S} (d z : Scalar S) →
  (d + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) z) + z ≡ d
qDenRemove_v147 = qNumRemove_v147

qQuotientDeletion_v147 : ∀ {S} (n d y z : Scalar S) →
  zero < d →
  zero < d + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) z →
  y * d < n * z →
  n * SmoothAlgebra.recip S d <
    (n + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) y) *
      SmoothAlgebra.recip S
        (d + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) z)
qQuotientDeletion_v147 = qQuotientDeletion_v147

qProjectionRetractionCI_v147 : ∀ {S n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (budget : Scalar S)
  (p x : VecS S n) →
  (∀ i → zero ≤ indexV p i) →
  weightedExposure_v147 p x ≤ budget →
  QRun_v142.projection (qRun_v142 D budget p x) ≡ p
qProjectionRetractionCI_v147 = qProjectionRetraction_v147

qTerminalMultiplierUniqueCI_v147 : ∀ {S n}
  (a b d n1 n2 : Scalar S) →
  zero < d →
  a * d ≡ n1 →
  b * d ≡ n2 →
  n1 ≡ n2 →
  a ≡ b
qTerminalMultiplierUniqueCI_v147 = qTerminalMultiplierUnique_v147

qTerminalProjectionUniqueCI_v147 : ∀ {S n}
  (t u : QTerminalSolution_v147 S n) →
  QTerminalSolution_v147.alpha t ≡ QTerminalSolution_v147.alpha u →
  QTerminalSolution_v147.x t ≡ QTerminalSolution_v147.x u →
  QTerminalSolution_v147.multiplier t ≡ QTerminalSolution_v147.multiplier u →
  QTerminalSolution_v147.projection t ≡ QTerminalSolution_v147.projection u
qTerminalProjectionUniqueCI_v147 = qTerminalProjectionUnique_v147

tbpttForwardAppendCI_v147 : ∀ {S input hidden m n}
  (block : LSTMBlock S input hidden)
  (state : LSTMState S hidden)
  (xs : Vec (VecS S input) m)
  (ys : Vec (VecS S input) n) →
  lstmRun_v146 block state (appendV_v146 xs ys) ≡
  lstmRun_v146 block (lstmRun_v146 block state xs) ys
tbpttForwardAppendCI_v147 = lstmForwardAppend_v147

tbpttReverseAppendCI_v147 : ∀ {S A m n}
  (fs : Vec (LocalVJP_v146 S A) m)
  (gs : Vec (LocalVJP_v146 S A) n)
  (x : A)
  (c : Scalar S) →
  localVJPChain_v146 (appendV_v146 fs gs) x c ≡
  localVJPChain_v146 fs x
    (localVJPChain_v146 gs (localVJPForward_v147 fs x) c)
tbpttReverseAppendCI_v147 = localVJPChainAppend_v147

------------------------------------------------------------------------
-- Explicit bridge status remains conservative.
------------------------------------------------------------------------

data BridgeStatus_v147 : Set where
  Established_v147 : BridgeStatus_v147
  Candidate_v147 : BridgeStatus_v147

bridgeTBPTTToEfficientCHAD_v147 : BridgeStatus_v147
bridgeTBPTTToEfficientCHAD_v147 = Established_v147

bridgeMetaSignToAlphaOrder_v147 : BridgeStatus_v147
bridgeMetaSignToAlphaOrder_v147 = Candidate_v147

bridgeAlphaOrderToQBudget_v147 : BridgeStatus_v147
bridgeAlphaOrderToQBudget_v147 = Candidate_v147

bridgeQProjectionToCoupledL2_v147 : BridgeStatus_v147
bridgeQProjectionToCoupledL2_v147 = Candidate_v147

bridgeCoupledL2ToSign_v147 : BridgeStatus_v147
bridgeCoupledL2ToSign_v147 = Candidate_v147
