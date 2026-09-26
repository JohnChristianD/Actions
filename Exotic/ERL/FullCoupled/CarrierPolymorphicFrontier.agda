{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Carrier-polymorphic frontier semantics.
--
-- This module adds an exact generic strict-progress theorem excluding
-- positive finite cycles without requiring a clock coordinate.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.CarrierPolymorphicFrontier where

open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Data.Empty using (⊥)
open import Data.Nat using (Nat; zero; suc; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (<-trans; <-irrefl; +-identityʳ; +-suc)
import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C

iterateStep :
  ∀ {State : Set} →
  (State → State) →
  Nat →
  State →
  State
iterateStep step zero s = s
iterateStep step (suc n) s = step (iterateStep step n s)

record StrictProgressWitness
  (State Measure : Set)
  (step : State → State)
  (_<_ : Measure → Measure → Set) : Set₁ where
  constructor strictProgressWitness
  field
    measure : State → Measure
    stepProgress :
      ∀ s →
      measure s < measure (step s)
    transitive :
      ∀ {a b c} →
      a < b →
      b < c →
      a < c
    irreflexive :
      ∀ a → ¬ (a < a)

record StrictProgressRelation
  (Measure : Set)
  (_<_ : Measure → Measure → Set) : Set₁ where
  constructor strictProgressRelation
  field
    isTransitive :
      ∀ {a b c} →
      a < b →
      b < c →
      a < c
    isIrreflexive :
      ∀ a → ¬ (a < a)

strictProgressRelation-from-witness :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_) →
  StrictProgressRelation Measure _<_
strictProgressRelation-from-witness W =
  strictProgressRelation
    (transitive W)
    (irreflexive W)

strictProgressWitness-from-relation :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (R : StrictProgressRelation Measure _<_)
  (measure : State → Measure)
  (stepProgress :
    ∀ s → measure s < measure (step s)) →
  StrictProgressWitness State Measure step _<_
strictProgressWitness-from-relation R measure stepProgress =
  strictProgressWitness
    measure
    stepProgress
    (StrictProgressRelation.isTransitive R)
    (StrictProgressRelation.isIrreflexive R)

open StrictProgressWitness public

strictProgressAfterIterate :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_)
  (n : Nat)
  (s : State) →
  measure W s <
  measure W (iterateStep step (suc n) s)
strictProgressAfterIterate W zero s =
  stepProgress W s
strictProgressAfterIterate W (suc n) s =
  transitive W
    (stepProgress W s)
    (strictProgressAfterIterate W n (step s))

noPositiveFiniteCycleFromStrictProgress :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_)
  (n : Nat)
  (s : State) →
  iterateStep step (suc n) s ≡ s →
  ⊥
noPositiveFiniteCycleFromStrictProgress W n s eq =
  irreflexive W
    (measure W s)
    (subst
      (λ t → measure W s < measure W t)
      eq
      (strictProgressAfterIterate W n s))


record NatSuccessorProgressWitness
  (State : Set)
  (step : State → State)
  (measure : State → Nat) : Set₁ where
  constructor natSuccessorProgressWitness
  field
    successor :
      ∀ s →
      measure (step s) ≡ suc (measure s)

open NatSuccessorProgressWitness public

sucInjective :
  ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
sucInjective refl = refl

natPlusLeftCancel :
  ∀ (k m n : Nat) → k + m ≡ k + n → m ≡ n
natPlusLeftCancel zero m n eq = eq
natPlusLeftCancel (suc k) m n eq =
  natPlusLeftCancel k m n (sucInjective eq)

successorMeasureAfterIterate :
  ∀ {State : Set}
  {step : State → State}
  {measure : State → Nat}
  (W : NatSuccessorProgressWitness State step measure)
  (n : Nat)
  (s : State) →
  measure (iterateStep step n s) ≡ measure s + n
successorMeasureAfterIterate W zero s =
  sym (+-identityʳ (measure W s))
successorMeasureAfterIterate W (suc n) s =
  trans
    (successor W (iterateStep (step W) n s))
    (trans
      (cong suc (successorMeasureAfterIterate W n s))
      (sym (+-suc (measure W s) n)))

successorMeasureOrbitInjective :
  ∀ {State : Set}
  {step : State → State}
  {measure : State → Nat}
  (W : NatSuccessorProgressWitness State step measure)
  (s : State)
  {m n : Nat} →
  iterateStep step m s ≡ iterateStep step n s →
  m ≡ n
successorMeasureOrbitInjective W s {m} {n} eq =
  natPlusLeftCancel
    (measure W s)
    m
    n
    (trans
      (sym (successorMeasureAfterIterate W m s))
      (trans
        (cong (measure W) eq)
        (successorMeasureAfterIterate W n s)))

natSucProgress : ∀ n → n < suc n
natSucProgress zero = s≤s z≤n
natSucProgress (suc n) = s≤s (natSucProgress n)

canonicalTotalCountStepProgress :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (s : C.FullLearnerState A) →
  C.totalCount (C.lcbCounts s) <
  C.totalCount (C.lcbCounts (C.canonicalFullStep K s))
canonicalTotalCountStepProgress K s =
  subst
    (λ t → C.totalCount (C.lcbCounts s) < t)
    (C.canonicalTotalCountStep K s)
    (natSucProgress (C.totalCount (C.lcbCounts s)))

canonicalTotalCountStrictProgress :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A) →
  StrictProgressWitness
    (C.FullLearnerState A)
    Nat
    (C.canonicalFullStep K)
    _<_
canonicalTotalCountStrictProgress K =
  strictProgressWitness
    (λ s → C.totalCount (C.lcbCounts s))
    (λ s → canonicalTotalCountStepProgress K s)
    <-trans
    <-irrefl

canonicalNoPositiveCycleFromTotalCount :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (n : Nat)
  (s : C.FullLearnerState A) →
  iterateStep (C.canonicalFullStep K) (suc n) s ≡ s →
  ⊥
canonicalNoPositiveCycleFromTotalCount K n s =
  noPositiveFiniteCycleFromStrictProgress
    (canonicalTotalCountStrictProgress K)
    n
    s
