{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteSemidirectComposition where

open import Agda.Builtin.Equality using (_≡_; refl; trans)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Finite semidirect-product theorem surface.
-- A monoid B acts on A by endomorphisms. The combined carrier is A × B
-- with the usual semidirect multiplication. The construction needs no
-- continuous O(2^n) or PSL(2,R) object.
------------------------------------------------------------------------

record Monoid (A : Set) : Set₁ where
  constructor monoid
  field
    unit : A
    mul : A → A → A
    assoc : ∀ x y z → mul (mul x y) z ≡ mul x (mul y z)
    left-id : ∀ x → mul unit x ≡ x
    right-id : ∀ x → mul x unit ≡ x

open Monoid public

record Action (A B : Set) (MA : Monoid A) (MB : Monoid B) : Set₁ where
  constructor action
  field
    act : B → A → A
    unit-law : ∀ a → act (unit MB) a ≡ a
    mul-law : ∀ b₁ b₂ a →
      act (mul MB b₁ b₂) a ≡ act b₁ (act b₂ a)

open Action public

record Semidirect (A B : Set) : Set₁ where
  constructor semidirect
  field
    left : Monoid A
    right : Monoid B
    actionLaw : Action A B left right

open Semidirect public

semidirectMul :
  ∀ {A B : Set} (S : Semidirect A B) →
  (A × B) → (A × B) → (A × B)
semidirectMul S (a₁ , b₁) (a₂ , b₂) =
  mul (left S) a₁ (act (actionLaw S) b₁ a₂) ,
  mul (right S) b₁ b₂

semidirect-left-factor :
  ∀ {A B : Set} (S : Semidirect A B) (a₁ a₂ : A) (b₁ : B) →
  semidirectMul S (a₁ , b₁) (a₂ , unit (right S))
  ≡
  (mul (left S) a₁ (act (actionLaw S) b₁ a₂) , b₁)
semidirect-left-factor S a₁ a₂ b₁ = refl
