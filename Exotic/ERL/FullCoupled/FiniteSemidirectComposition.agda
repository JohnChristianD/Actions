{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteSemidirectComposition where

open import Agda.Builtin.Equality using (_≡_; refl; trans; sym; cong)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Finite semidirect-product theorem surface.
-- A monoid B acts on A by endomorphisms. The combined carrier is A × B
-- with the standard semidirect multiplication. No continuous group object
-- is smuggled into the finite kernel.
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

semidirect-assoc :
  ∀ {A B : Set} (S : Semidirect A B)
  (x y z : A × B) →
  semidirectMul S (semidirectMul S x y) z
  ≡
  semidirectMul S x (semidirectMul S y z)
semidirect-assoc S (a₁ , b₁) (a₂ , b₂) (a₃ , b₃) =
  cong
    (λ a → a , mul (right S) (mul (right S) b₁ b₂) b₃)
    first
  where
  actS = actionLaw S
  MA = left S
  MB = right S

  first₀ :
    mul MA
      (mul MA a₁ (act actS b₁ a₂))
      (act actS (mul MB b₁ b₂) a₃)
    ≡
    mul MA a₁
      (mul MA (act actS b₁ a₂)
        (act actS (mul MB b₁ b₂) a₃))
  first₀ = assoc MA a₁ (act actS b₁ a₂) (act actS (mul MB b₁ b₂) a₃)

  first₁ :
    mul MA a₁
      (mul MA (act actS b₁ a₂)
        (act actS (mul MB b₁ b₂) a₃))
    ≡
    mul MA a₁
      (mul MA (act actS b₁ a₂)
        (act actS b₁ (act actS b₂ a₃)))
  first₁ =
    cong
      (λ q → mul MA a₁
        (mul MA (act actS b₁ a₂) q))
      (mul-law actS b₁ b₂ a₃)

  first₂ :
    mul MA a₁
      (mul MA (act actS b₁ a₂)
        (act actS b₁ (act actS b₂ a₃)))
    ≡
    mul MA a₁
      (act actS b₁
        (mul MA a₂ (act actS b₂ a₃)))
  first₂ =
    cong
      (λ q → mul MA a₁ q)
      (sym (mul-law-act-internal actS MA b₁ a₂ (act actS b₂ a₃)))

  mul-law-act-internal :
    ∀ (actS : Action A B MA MB) (MA : Monoid A)
      (b : B) (a c : A) →
    mul MA (act actS b a) (act actS b c)
    ≡ act actS b (mul MA a c)
  mul-law-act-internal actS′ MA′ b a c =
    -- The standard semidirect multiplication requires the action to be a
    -- monoid endomorphism of A. The original Action record deliberately did
    -- not contain that axiom, so associativity is not derivable yet.
    -- Keep this boundary explicit rather than postulating it.
    {!!}
