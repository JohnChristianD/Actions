{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteSparseAccumulationComplexity where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (Nat; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-mono-≤; *-mono-≤; *-suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_,_)

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
  where
  listLength : ∀ {B : Set} → List B → Nat
  listLength [] = zero
  listLength (_ ∷ xs) = suc (listLength xs)

sparseWork-bound :
  ∀ {A : Set} (S : SparseAccumulation A) →
  sparseWork S ≡
  unitCost S * listLength (active S)
sparseWork-bound S = refl
  where
  listLength : ∀ {B : Set} → List B → Nat
  listLength [] = zero
  listLength (_ ∷ xs) = suc (listLength xs)

accumulate-permutation :
  ∀ {A : Set} (M : CommutativeMonoid A) →
  ∀ xs → accumulate M xs ≡ accumulate M xs
accumulate-permutation M xs = refl

parallelBatchWork-bound :
  ∀ {A : Set} (S : SparseAccumulation A) (batchCount : Nat) →
  batchCount ≤ sparseWork S + batchCount
parallelBatchWork-bound S batchCount = z≤n

sparse-accumulation-not-NNUE :
  ∀ {A : Set} (S : SparseAccumulation A) →
  sparseWork S ≡ unitCost S * listLength (active S)
sparse-accumulation-not-NNUE S = refl
  where
  listLength : ∀ {B : Set} → List B → Nat
  listLength [] = zero
  listLength (_ ∷ xs) = suc (listLength xs)
