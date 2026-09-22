{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ExactBoundedFactorLiftTheorems where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Data.Nat using (Nat; suc)
open import Data.Fin using (toℕ)
open import Data.Fin.Properties using (toℕ-bounded)
open import Function.Definitions using (Injective)

open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.FiniteUniversalBoundary as B

------------------------------------------------------------------------
-- Exact bounded-factor / injective-lift layer.
--
-- The F4 theta coordinate is represented by Int8 = Fin 256.  Therefore
-- every exact canonical orbit has a uniformly bounded theta projection.
-- This is a representation/coercion theorem, not an L2-contraction claim.
------------------------------------------------------------------------

canonicalF4ThetaQ-bounded :
  ∀ {A} (K : C.FullLearnerKernel A)
    (s : C.FullLearnerState A) (n : Nat) →
  toℕ (C.code
    (C.thetaQ
      (C.optimizer
        (C.iterateCanonical K n s)))) < 256
canonicalF4ThetaQ-bounded K s n =
  toℕ-bounded
    (C.code
      (C.thetaQ
        (C.optimizer
          (C.iterateCanonical K n s))))

------------------------------------------------------------------------
-- The bounded F4 projection cannot be injective on the unbounded Nat
-- orbit index.  This is the exact finite-carrier obstruction, now applied
-- to the canonical F4 projection itself.
------------------------------------------------------------------------

canonicalF4ThetaQ-not-orbit-injective :
  ∀ {A} (K : C.FullLearnerKernel A)
    (s : C.FullLearnerState A) →
  ¬ Injective _≡_ _≡_
    (λ n →
      C.code
        (C.thetaQ
          (C.optimizer
            (C.iterateCanonical K n s))))
canonicalF4ThetaQ-not-orbit-injective K s =
  B.finiteCarrier-not-injective-on-unbounded-clock
    (λ n →
      C.code
        (C.thetaQ
          (C.optimizer
            (C.iterateCanonical K n s))))

------------------------------------------------------------------------
-- Exact separation theorem:
--
-- finite F4 recurrence is compatible with full-state aperiodicity.
-- If a finite factor were injective on the exact orbit, then its
-- recurrence would force equality of orbit indices; the positive-time
-- recurrence is therefore impossible.  No cancellation of the
-- existing full-state no-cycle theorem is used.
------------------------------------------------------------------------

finiteFactor-recurrence-lift-impossible :
  ∀ {S F : Set}
    (orbit : Nat → S)
    (factor : S → F)
    (factorInjectiveOnOrbit :
      ∀ {m n : Nat} →
      factor (orbit m) ≡ factor (orbit n) →
      m ≡ n)
    {n p : Nat} →
    factor (orbit n) ≡ factor (orbit (n + suc p)) →
    ⊥
finiteFactor-recurrence-lift-impossible
  orbit factor factorInjectiveOnOrbit {n} {p} eq =
  nat-suc-not-equal
    (factorInjectiveOnOrbit eq)

------------------------------------------------------------------------
-- Endogenous bounded-factor / exact-injective-lift theorem.
--
-- The canonical orbit is index-injective, while its F4 theta projection
-- is not index-injective.  Hence repeated F4 representations necessarily
-- correspond to distinct full states.
------------------------------------------------------------------------

canonicalF4-recurrence-is-not-full-recurrence :
  ∀ {A} (K : C.FullLearnerKernel A)
    (s : C.FullLearnerState A)
    {m n : Nat} →
  C.code
    (C.thetaQ
      (C.optimizer
        (C.iterateCanonical K m s)))
  ≡
  C.code
    (C.thetaQ
      (C.optimizer
        (C.iterateCanonical K n s))) →
  m ≢ n →
  C.iterateCanonical K m s ≢ C.iterateCanonical K n s
canonicalF4-recurrence-is-not-full-recurrence K s {m} {n} fEq mNeq fullEq =
  mNeq (C.canonicalOrbit-state-injective K s
    (cong C.clock fullEq))
