{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CIInterpolation_v147 where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Exotic.ERL.FullCoupled.CompleteSafe_v147

------------------------------------------------------------------------
-- Canonical algebraic interoperability surface.
--
-- Kernel-facing names in this layer describe mathematical structure rather
-- than a benchmark, environment, paper author, or implementation vendor.
-- Environment-specific adapters and provenance belong outside the theorem
-- namespace. Every theorem below is an existing proof term from
-- CompleteSafe_v147 or a direct finite ring derivation. No oracle result is
-- promoted to proof.
------------------------------------------------------------------------

qNumRemove_v147 : ∀ {S} (n y : Scalar S) →
  (n + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) y) + y ≡ n
qNumRemove_v147 n y =
  trans
    (Ring.addAssoc (OrderedRing.ring (SmoothAlgebra.orderedRing _)) n
      (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _)) y) y)
    (trans
      (cong
        (λ t → n + t)
        (Ring.addNegL (OrderedRing.ring (SmoothAlgebra.orderedRing _)) y))
      (Ring.addZeroR (OrderedRing.ring (SmoothAlgebra.orderedRing _)) n))

qDenRemove_v147 : ∀ {S} (d z : Scalar S) →
  (d + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) z) + z ≡ d
qDenRemove_v147 d z =
  qNumRemove_v147 d z

qQuotientDeletion_v147 : ∀ {S} (n d y z : Scalar S) →
  zero < d →
  zero < d + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) z →
  y * d < n * z →
  n * SmoothAlgebra.recip S d <
    (n + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) y) *
      SmoothAlgebra.recip S
        (d + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) z)
qQuotientDeletion_v147 = multiplierDeletionStrict_v142

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

record CIAlgebraicInterpolation_v147 (S : SmoothAlgebra) : Set₁ where
  field
    qNumRemove : ∀ n y →
      (n + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) y) + y ≡ n
    qDenRemove : ∀ d z →
      (d + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) z) + z ≡ d
    qQuotientDeletion : ∀ n d y z →
      zero < d →
      zero < d + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) z →
      y * d < n * z →
      n * SmoothAlgebra.recip S d <
        (n + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) y) *
          SmoothAlgebra.recip S
            (d + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) z)
    qProjectionRetraction : ∀ {n}
      (D : QProjectionDecisionAlgebra_v140 S)
      (budget : Scalar S)
      (p x : VecS S n) →
      (∀ i → zero ≤ indexV p i) →
      weightedExposure_v147 p x ≤ budget →
      QRun_v142.projection (qRun_v142 D budget p x) ≡ p
    qTerminalMultiplierUnique : ∀ {n}
      (a b d n1 n2 : Scalar S) →
      zero < d →
      a * d ≡ n1 →
      b * d ≡ n2 →
      n1 ≡ n2 →
      a ≡ b
    qTerminalProjectionUnique : ∀ {n}
      (t u : QTerminalSolution_v147 S n) →
      QTerminalSolution_v147.alpha t ≡ QTerminalSolution_v147.alpha u →
      QTerminalSolution_v147.x t ≡ QTerminalSolution_v147.x u →
      QTerminalSolution_v147.multiplier t ≡ QTerminalSolution_v147.multiplier u →
      QTerminalSolution_v147.projection t ≡ QTerminalSolution_v147.projection u
    tbpttForwardAppend : ∀ {input hidden m n}
      (block : LSTMBlock S input hidden)
      (state : LSTMState S hidden)
      (xs : Vec (VecS S input) m)
      (ys : Vec (VecS S input) n) →
      lstmRun_v146 block state (appendV_v146 xs ys) ≡
      lstmRun_v146 block (lstmRun_v146 block state xs) ys
    tbpttReverseAppend : ∀ {A m n}
      (fs : Vec (LocalVJP_v146 S A) m)
      (gs : Vec (LocalVJP_v146 S A) n)
      (x : A)
      (c : Scalar S) →
      localVJPChain_v146 (appendV_v146 fs gs) x c ≡
      localVJPChain_v146 fs x
        (localVJPChain_v146 gs (localVJPForward_v147 fs x) c)

ciAlgebraicInterpolation_v147 : ∀ {S} → CIAlgebraicInterpolation_v147 S
ciAlgebraicInterpolation_v147 = record
  { qNumRemove = qNumRemove_v147
  ; qDenRemove = qDenRemove_v147
  ; qQuotientDeletion = qQuotientDeletion_v147
  ; qProjectionRetraction = qProjectionRetractionCI_v147
  ; qTerminalMultiplierUnique = qTerminalMultiplierUniqueCI_v147
  ; qTerminalProjectionUnique = qTerminalProjectionUniqueCI_v147
  ; tbpttForwardAppend = tbpttForwardAppendCI_v147
  ; tbpttReverseAppend = tbpttReverseAppendCI_v147
  }

------------------------------------------------------------------------
-- Cross-layer bridge classification.
-- Established = kernel-checked here; candidate = requires a new proof.
-- The classification is non-semantic provenance and does not certify a
-- benchmark, environment, author, or external empirical result.
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
