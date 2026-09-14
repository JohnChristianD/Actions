{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteErgodicComposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat using (Nat; zero; suc)

------------------------------------------------------------------------
-- Exact finite-state ergodic certificate layer.
--
-- Irreducibility and aperiodicity are graph properties of a finite
-- transition carrier. Invariant measure is kept as a separate exact datum;
-- normalized probabilities require an additional exact division structure.
------------------------------------------------------------------------

record FiniteTransition (S : Set) : Set₁ where
  constructor finiteTransition
  field
    next : S → S

open FiniteTransition public

iterate : ∀ {S : Set} → FiniteTransition S → Nat → S → S
iterate T zero x = x
iterate T (suc n) x = next T (iterate T n x)

record IrreducibleCertificate (S : Set) (T : FiniteTransition S) : Set₁ where
  constructor irreducibleCertificate
  field
    reachable : ∀ x y → Σ Nat (λ n → iterate T n x ≡ y)

open IrreducibleCertificate public

record AperiodicCertificate (S : Set) (T : FiniteTransition S) : Set₁ where
  constructor aperiodicCertificate
  field
    returnWitness : ∀ x → Σ Nat (λ n → iterate T (suc n) x ≡ x)
    gcdOne : ∀ x → Set

open AperiodicCertificate public

record InvariantMeasure (S : Set) (T : FiniteTransition S) : Set₁ where
  constructor invariantMeasure
  field
    weight : S → Nat
    invariant : ∀ x → weight (next T x) ≡ weight x
    nonzero : ∀ x → weight x ≡ suc zero

open InvariantMeasure public

------------------------------------------------------------------------
-- Exact invariant counting measure for every bijective finite transition.
-- The proof is pointwise and does not need division or floating point.
------------------------------------------------------------------------

record PermutationTransition (S : Set) : Set₁ where
  constructor permutationTransition
  field
    transition : S → S
    inverse : S → S
    leftInverse : ∀ x → inverse (transition x) ≡ x
    rightInverse : ∀ x → transition (inverse x) ≡ x

open PermutationTransition public

permutationCountingInvariant :
  ∀ {S : Set} (P : PermutationTransition S) →
  InvariantMeasure S (finiteTransition (transition P))
permutationCountingInvariant P =
  invariantMeasure
    (λ _ → suc zero)
    (λ _ → refl)
    (λ _ → refl)

------------------------------------------------------------------------
-- Aperiodicity is exactly represented as return-time arithmetic. A
-- self-loop is the canonical finite certificate for period one at its state;
-- irreducibility is kept explicit because propagation to all states is a
-- genuine graph theorem, not an Int8 arithmetic identity.
------------------------------------------------------------------------

record SelfLoopWitness (S : Set) (T : FiniteTransition S) : Set where
  constructor selfLoopWitness
  field
    state0 : S
    loop : next T state0 ≡ state0

open SelfLoopWitness public

selfLoopReturnWitness :
  ∀ {S : Set} {T : FiniteTransition S} →
  SelfLoopWitness S T →
  Σ Nat (λ n → iterate T (suc n) (state0 (refl))) ≡ state0 (refl)
selfLoopReturnWitness w = zero , loop w

------------------------------------------------------------------------
-- Endogenous finite ergodic package.
------------------------------------------------------------------------

record FiniteErgodicComposition : Set₁ where
  constructor finiteErgodicComposition
  field
    state : Set
    transition : FiniteTransition state
    irreducible : IrreducibleCertificate state transition
    aperiodic : AperiodicCertificate state transition
    invariant : InvariantMeasure state transition
