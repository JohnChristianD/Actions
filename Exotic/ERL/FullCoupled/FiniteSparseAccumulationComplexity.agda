{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteSparseAccumulationComplexity where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (Nat; zero; suc; _+_; _*_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n*m; <⇒≱)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (ℕ→Fin-notInjective)
open import Data.List.Base using (List; []; _∷_)
open import Function.Definitions using (Injective)

record CommutativeMonoid (A : Set) : Set where
  constructor commutativeMonoid
  field
    ε : A
    _⊕_ : A → A → A
    identityˡ : ∀ x → ε ⊕ x ≡ x
    identityʳ : ∀ x → x ⊕ ε ≡ x
    assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
    comm : ∀ x y → x ⊕ y ≡ y ⊕ x
open CommutativeMonoid public

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

repeat : ∀ {A : Set} → Nat → A → List A
repeat zero x = []
repeat (suc n) x = x ∷ repeat n x

accumulate : ∀ {A : Set} → CommutativeMonoid A → List A → A
accumulate M [] = ε M
accumulate M (x ∷ xs) = _⊕_ M x (accumulate M xs)

record SparseAccumulation (A : Set) : Set where
  constructor sparseAccumulation
  field
    monoid : CommutativeMonoid A
    active : List A
    unitCost : Nat
open SparseAccumulation public

sparseWork : ∀ {A : Set} → SparseAccumulation A → Nat
sparseWork S = unitCost S * listLength (active S)

sparseWork-bound :
  ∀ {A : Set} (S : SparseAccumulation A) →
  sparseWork S ≡
  unitCost S * listLength (active S)
sparseWork-bound S = refl

sparseWork-repeat-exact :
  ∀ {A : Set} (M : CommutativeMonoid A) (x : A)
  (unitCost : Nat) (k : Nat) →
  sparseWork (sparseAccumulation M (repeat k x) unitCost) ≡
  unitCost * k
sparseWork-repeat-exact M x unitCost k = refl

positive-unit-cost-is-unbounded :
  ∀ {A : Set} (M : CommutativeMonoid A) (x : A)
  (positiveUnitCost : Nat) (B : Nat) →
  B <
  sparseWork
    (sparseAccumulation M (repeat (suc B) x) (suc positiveUnitCost))
positive-unit-cost-is-unbounded M x positiveUnitCost B =
  m≤n*m (suc B) (suc positiveUnitCost)

no-uniform-positive-sparse-work-bound :
  ∀ {A : Set} (M : CommutativeMonoid A) (x : A)
  (positiveUnitCost : Nat) →
  ¬ (∃ λ B →
       ∀ xs →
       sparseWork (sparseAccumulation M xs (suc positiveUnitCost)) ≤ B)
no-uniform-positive-sparse-work-bound M x positiveUnitCost
  (B , bound) =
  <⇒≱
    (positive-unit-cost-is-unbounded M x positiveUnitCost B)
    (bound (repeat (suc B) x))

finite-sparse-repetition-not-injective :
  ∀ {n : Nat}
  (M : CommutativeMonoid (Fin n)) (x : Fin n) →
  ¬ Injective _≡_ _≡_
    (λ k → accumulate M (repeat k x))
finite-sparse-repetition-not-injective M x =
  ℕ→Fin-notInjective (λ k → accumulate M (repeat k x))

finite-sparse-length-decoder-impossible :
  ∀ {n : Nat}
  (M : CommutativeMonoid (Fin n)) (x : Fin n)
  (decode : Fin n → Nat) →
  ¬ (∀ k →
     decode (accumulate M (repeat k x)) ≡ k)
finite-sparse-length-decoder-impossible M x decode sound =
  finite-sparse-repetition-not-injective M x
    (λ {i} {j} collision →
      trans
        (sym (sound i))
        (trans (cong decode collision) (sound j)))

parallelBatchWork-bound :
  ∀ {A : Set} (S : SparseAccumulation A) (batchCount : Nat) →
  batchCount ≤ sparseWork S + batchCount
parallelBatchWork-bound S batchCount = z≤n

accumulate-self :
  ∀ {A : Set} (M : CommutativeMonoid A) →
  ∀ xs → accumulate M xs ≡ accumulate M xs
accumulate-self M xs = refl
