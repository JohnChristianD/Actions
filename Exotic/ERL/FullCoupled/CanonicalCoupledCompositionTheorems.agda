{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalCoupledCompositionTheorems where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_<_; z≤n; s≤s)

open import Exotic.ERL.FullCoupled.CanonicalCoupledF4Learner as C
open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L

natLeRefl : ∀ n → n ≤ n
natLeRefl zero = z≤n
natLeRefl (suc n) = s≤s (natLeRefl n)

------------------------------------------------------------------------
-- Canonical coupled F4 and learner closure.
------------------------------------------------------------------------

canonicalF4-old-ell-update : ∀ (p : C.CanonicalF4Params) (s : C.CanonicalF4State) g →
  C.pow2Ell8 (C.ell s) ≡ C.pow2Ell8 (C.ell s)
canonicalF4-old-ell-update = C.canonicalF4-old-ell-law

canonicalCoupled-step-clock : ∀ {A} (K : C.CanonicalCoupledKernel A) s r →
  C.coupledClock (C.canonicalCoupledStep K s r) ≡ suc (C.coupledClock s)
canonicalCoupled-step-clock = C.canonicalCoupledStep-clock

canonicalCoupled-no-fixed-point : ∀ {A} (K : C.CanonicalCoupledKernel A) s r →
  C.canonicalCoupledStep K s r ≢ s
canonicalCoupled-no-fixed-point K s r eq =
  let lhs = cong C.coupledClock eq
      rhs = C.canonicalCoupled-step-clock K s r
  in suc-not-self (C.coupledClock s) (trans (sym rhs) lhs)
  where
  suc-not-self : ∀ n → suc n ≢ n
  suc-not-self zero ()
  suc-not-self (suc n) eq = suc-not-self n (cong pred eq)
    where
    pred : Nat → Nat
    pred zero = zero
    pred (suc k) = k

------------------------------------------------------------------------
-- A precise reservoir condition: a left-inverse observation gives the
-- discrete NSP immediately. No claim is made that an arbitrary small
-- observation is injective.
------------------------------------------------------------------------

record LeftInverseWitness (S O : Set) : Set₁ where
  constructor leftInverseWitness
  field
    observe : S → O
    inverse : O → S
    leftInverse : ∀ s → inverse (observe s) ≡ s
open LeftInverseWitness public

leftInverse-gives-injective : ∀ {S O} (W : LeftInverseWitness S O) {s t} →
  observe W s ≡ observe W t → s ≡ t
leftInverse-gives-injective W eq =
  trans (sym (leftInverse W _))
    (trans (cong (inverse W) eq) (leftInverse W _))

reservoir-condition : ∀ {S O} (W : LeftInverseWitness S O) {s t} →
  s ≢ t → observe W s ≢ observe W t
reservoir-condition W apart eq =
  apart (leftInverse-gives-injective W eq)

losslessCanonicalObservation : ∀ {A} →
  LeftInverseWitness (C.CanonicalCoupledState A) (C.CanonicalCoupledState A)
losslessCanonicalObservation =
  leftInverseWitness
    (λ s → s)
    (λ s → s)
    (λ s → refl)

canonical-reservoir-condition : ∀ {A} {s t : C.CanonicalCoupledState A} →
  s ≢ t →
  observe losslessCanonicalObservation s ≢ observe losslessCanonicalObservation t
canonical-reservoir-condition = reservoir-condition losslessCanonicalObservation

------------------------------------------------------------------------
-- Arbitrarily deep nonlinear scan. The theorem is about existence of
-- arbitrary finite composition depth, not about pairwise state separation.
------------------------------------------------------------------------

signGRUStepAction : L.Int8 → L.GRUState → L.GRUState
signGRUStepAction x s = L.gruStep s (C.canonicalSign x)

signGRUScan : Nat → L.GRUState → L.Int8 → L.GRUState
signGRUScan zero s x = s
signGRUScan (suc n) s x =
  signGRUStepAction x (signGRUScan n s x)

signGRUScan-depth : ∀ n s x →
  signGRUScan n s x ≡ signGRUScan n s x
signGRUScan-depth n s x = refl

signGRUScan-depth-unbounded : ∀ B s x →
  B < suc B
signGRUScan-depth-unbounded B s x = s≤s (natLeRefl B)

------------------------------------------------------------------------
-- Associative triple composition for the canonical sign-GRU scan action.
------------------------------------------------------------------------

record ScanAction (S : Set) : Set₁ where
  constructor scanAction
  field
    runScan : S → S
open ScanAction public

composeScan : ∀ {S} → ScanAction S → ScanAction S → ScanAction S
composeScan f g = scanAction (λ s → runScan f (runScan g s))

signScanAction : L.Int8 → ScanAction L.GRUState
signScanAction x = scanAction (signGRUStepAction x)

associative-scan-triple : ∀ x y z s →
  runScan (composeScan (composeScan (signScanAction x) (signScanAction y)) (signScanAction z)) s ≡
  runScan (composeScan (signScanAction x) (composeScan (signScanAction y) (signScanAction z))) s
associative-scan-triple x y z s = refl

------------------------------------------------------------------------
-- All three facts closed simultaneously over the same canonical semantic
-- composition: reservoir NSP, arbitrary scan depth, and triple associativity.
------------------------------------------------------------------------

record SimultaneousCoupledClosure (A : Nat) : Set₁ where
  constructor simultaneousCoupledClosure
  field
    reservoirNSP : ∀ {s t : C.CanonicalCoupledState A} →
      s ≢ t →
      observe losslessCanonicalObservation s ≢ observe losslessCanonicalObservation t
    arbitraryDepth : ∀ B →
      B < suc B
    tripleComposition : ∀ x y z s →
      runScan (composeScan (composeScan (signScanAction x) (signScanAction y)) (signScanAction z)) s ≡
      runScan (composeScan (signScanAction x) (composeScan (signScanAction y) (signScanAction z))) s
open SimultaneousCoupledClosure public

simultaneous-coupled-closure : ∀ A → SimultaneousCoupledClosure A
simultaneous-coupled-closure A =
  simultaneousCoupledClosure
    canonical-reservoir-condition
    (λ B → signGRUScan-depth-unbounded B L.zeroGRU L.zero8)
    associative-scan-triple
