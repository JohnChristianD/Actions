{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteSemidirectComposition where

open import Agda.Builtin.Equality using (_≡_; refl; trans; sym; cong)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Finite semidirect-product theorem surface.
-- A monoid B acts on A by monoid endomorphisms. The combined carrier is
-- A × B with the standard semidirect multiplication.
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
    unit-preserving : ∀ b → act b (unit MA) ≡ unit MA
    mul-law : ∀ b₁ b₂ a →
      act (mul MB b₁ b₂) a ≡ act b₁ (act b₂ a)
    hom-law : ∀ b a₁ a₂ →
      act b (mul MA a₁ a₂) ≡ mul MA (act b a₁) (act b a₂)

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

pair-cong :
  ∀ {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} →
  a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
pair-cong refl refl = refl

semidirect-left-factor :
  ∀ {A B : Set} (S : Semidirect A B) (a₁ a₂ : A) (b₁ : B) →
  semidirectMul S (a₁ , b₁) (a₂ , unit (right S))
  ≡
  (mul (left S) a₁ (act (actionLaw S) b₁ a₂) , b₁)
semidirect-left-factor S a₁ a₂ b₁ = refl

semidirect-assoc :
  ∀ {A B : Set} (S : Semidirect A B)
  (x y z : A × B) →
  semidirectMul S (semidirectMul S x y) z
  ≡
  semidirectMul S x (semidirectMul S y z)
semidirect-assoc S (a₁ , b₁) (a₂ , b₂) (a₃ , b₃) =
  pair-cong first-final second-final
  where
  MA = left S
  MB = right S
  α = actionLaw S

  first₀ :
    mul MA
      (mul MA a₁ (act α b₁ a₂))
      (act α (mul MB b₁ b₂) a₃)
    ≡
    mul MA a₁
      (mul MA (act α b₁ a₂)
        (act α (mul MB b₁ b₂) a₃))
  first₀ = assoc MA a₁ (act α b₁ a₂) (act α (mul MB b₁ b₂) a₃)

  first₁ :
    mul MA a₁
      (mul MA (act α b₁ a₂)
        (act α (mul MB b₁ b₂) a₃))
    ≡
    mul MA a₁
      (mul MA (act α b₁ a₂)
        (act α b₁ (act α b₂ a₃)))
  first₁ =
    cong
      (λ q → mul MA a₁ (mul MA (act α b₁ a₂) q))
      (mul-law α b₁ b₂ a₃)

  first₂ :
    mul MA a₁
      (mul MA (act α b₁ a₂)
        (act α b₁ (act α b₂ a₃)))
    ≡
    mul MA a₁
      (act α b₁ (mul MA a₂ (act α b₂ a₃)))
  first₂ =
    cong
      (λ q → mul MA a₁ q)
      (sym (hom-law α b₁ a₂ (act α b₂ a₃)))

  first-final :
    mul MA
      (mul MA a₁ (act α b₁ a₂))
      (act α (mul MB b₁ b₂) a₃)
    ≡
    mul MA a₁
      (act α b₁ (mul MA a₂ (act α b₂ a₃)))
  first-final = trans first₀ (trans first₁ first₂)

  second-final :
    mul MB (mul MB b₁ b₂) b₃
    ≡
    mul MB b₁ (mul MB b₂ b₃)
  second-final = assoc MB b₁ b₂ b₃

semidirect-unit-left :
  ∀ {A B : Set} (S : Semidirect A B) (a : A) (b : B) →
  semidirectMul S (unit (left S) , unit (right S)) (a , b)
  ≡ (a , b)
semidirect-unit-left S a b =
  pair-cong
    (trans
      (cong (λ q → mul (left S) q (act (actionLaw S) (unit (right S)) a))
        (unit-law (actionLaw S) a))
      (left-id (left S) a))
    (left-id (right S) b)

semidirect-unit-right :
  ∀ {A B : Set} (S : Semidirect A B) (a : A) (b : B) →
  semidirectMul S (a , b) (unit (left S) , unit (right S))
  ≡ (a , b)
semidirect-unit-right S a b =
  pair-cong
    (trans
      (cong (λ q → mul (left S) a q)
        (unit-preserving (actionLaw S) b))
      (right-id (left S) a))
    (right-id (right S) b)
