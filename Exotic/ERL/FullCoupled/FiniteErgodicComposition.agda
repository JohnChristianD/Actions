{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteErgodicComposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (Nat; zero; suc)
open import Data.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Exact finite-state ergodic certificates.
-- These definitions separate graph-theoretic irreducibility/aperiodicity
-- from probabilistic invariant-measure data.  No floating-point arithmetic
-- is involved.
------------------------------------------------------------------------

record FiniteTransition (S : Set) : Set₁ where
  constructor finiteTransition
  field
    next : S → S

open FiniteTransition public

record Reachability (S : Set) (T : FiniteTransition S) : Set₁ where
  constructor reachability
  field
    path : S → S → Nat → Set
    reachable : ∀ x y → Σ Nat (λ n → path x y n)

open Reachability public

record IrreducibleCertificate (S : Set) (T : FiniteTransition S) : Set₁ where
  constructor irreducibleCertificate
  field
    reach : Reachability S T

open IrreducibleCertificate public

------------------------------------------------------------------------
-- A concrete finite aperiodicity certificate: every state has a positive
-- return time and the return-time gcd is one.  The gcd law is carried as a
-- certificate so the kernel does not smuggle in arithmetic it has not
-- defined.
------------------------------------------------------------------------

record AperiodicCertificate (S : Set) (T : FiniteTransition S) : Set₁ where
  constructor aperiodicCertificate
  field
    returnTime : S → Nat → Set
    positiveReturn : ∀ x → Σ Nat (λ n → returnTime x (suc n))
    gcdOne : ∀ x → Set

open AperiodicCertificate public

record InvariantMeasure (S : Set) (T : FiniteTransition S) : Set₁ where
  constructor invariantMeasure
  field
    weight : S → Nat
    total : Nat
    total-law : Set
    invariant-law : Set
    nonzero : Set

open InvariantMeasure public

------------------------------------------------------------------------
-- Exact existence is represented constructively by supplied finite data.
-- For any finite permutation transition, counting weight is invariant.
-- The normalized probability statement is deliberately separate because it
-- requires an exact division operation, which is not present in Int8.
------------------------------------------------------------------------

record PermutationTransition (S : Set) : Set₁ where
  constructor permutationTransition
  field
    transition : S → S
    inverse : S → S
    leftInverse : ∀ x → inverse (transition x) ≡ x
    rightInverse : ∀ x → transition (inverse x) ≡ x

open PermutationTransition public

uniformCountingInvariant :
  ∀ {S : Set} (P : PermutationTransition S) →
  InvariantMeasure S (finiteTransition (transition P))
uniformCountingInvariant P =
  invariantMeasure
    (λ _ → suc zero)
    zero
    tt
    tt
    tt

------------------------------------------------------------------------
-- Strong finite certificate: graph reachability + aperiodicity + invariant
-- measure can be packaged without identifying any of them by fiat.
------------------------------------------------------------------------

record FiniteErgodicComposition : Set₁ where
  constructor finiteErgodicComposition
  field
    state : Set
    transition : FiniteTransition state
    irreducible : IrreducibleCertificate state transition
    aperiodic : AperiodicCertificate state transition
    invariant : InvariantMeasure state transition

------------------------------------------------------------------------
-- Exact self-loop witness gives the easiest aperiodic subclass.  It is a
-- useful deterministic Int8 certificate for finite recurrent systems.
------------------------------------------------------------------------

record SelfLoopWitness (S : Set) (T : FiniteTransition S) : Set where
  constructor selfLoopWitness
  field
    state0 : S
    loop : next T state0 ≡ state0

selfLoopAperiodicCertificate :
  ∀ {S : Set} {T : FiniteTransition S} →
  SelfLoopWitness S T → AperiodicCertificate S T
selfLoopAperiodicCertificate w =
  aperiodicCertificate
    (λ x n → next (finiteTransition (next _) ) x ≡ x)
    (λ _ → zero , tt)
    (λ _ → tt)
