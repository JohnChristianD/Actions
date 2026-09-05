{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.AlgebraClosure_v147 where

open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong)
open import Exotic.ERL.FullCoupled.CompleteSafe_v147

------------------------------------------------------------------------
-- v147 constructive additive-algebra closure.
-- These identities are consequences of the finite Ring interface used by
-- the canonical ERL development; no external arithmetic or analysis is used.
------------------------------------------------------------------------

negNeg_v147 : ∀ {S} (x : Scalar S) →
  Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x)
  ≡ x
negNeg_v147 {S} x =
  sym
    (trans
      (sym (Ring.addZeroR
        (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x))
      (trans
        (cong
          (Ring._+_ (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x)
          (sym (Ring.addNegR
            (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x)))
        (trans
          (sym (Ring.addAssoc
            (OrderedRing.ring (SmoothAlgebra.orderedRing S))
            x
            (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x)
            (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
              (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x))))
          (trans
            (cong
              (λ t → Ring._+_ (OrderedRing.ring
                (SmoothAlgebra.orderedRing S)) t
                (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
                  (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x)))
              (Ring.addNegR
                (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x))
            (Ring.addZeroL
              (OrderedRing.ring (SmoothAlgebra.orderedRing S))
              (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
                (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x)))))))

negZero_v147 : ∀ {S} →
  Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (Ring.zero (OrderedRing.ring (SmoothAlgebra.orderedRing S)))
  ≡ Ring.zero (OrderedRing.ring (SmoothAlgebra.orderedRing S))
negZero_v147 {S} =
  trans
    (sym (Ring.addZeroR
      (OrderedRing.ring (SmoothAlgebra.orderedRing S))
      (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
        (Ring.zero (OrderedRing.ring (SmoothAlgebra.orderedRing S))))))
    (Ring.addNegL
      (OrderedRing.ring (SmoothAlgebra.orderedRing S))
      (Ring.zero (OrderedRing.ring (SmoothAlgebra.orderedRing S))))

addNegComm_v147 : ∀ {S} (x : Scalar S) →
  Ring._+_ (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x) x
  ≡
  Ring._+_ (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    x (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x)
addNegComm_v147 {S} x =
  Ring.addComm (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x) x

negNegZero_v147 : ∀ {S} →
  Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
      (Ring.zero (OrderedRing.ring (SmoothAlgebra.orderedRing S))))
  ≡ Ring.zero (OrderedRing.ring (SmoothAlgebra.orderedRing S))
negNegZero_v147 {S} = negNeg_v147 _
