{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteSemidirectComposition where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)

record Monoid (M : Set) : Set₁ where
  constructor monoid
  field
    unit : M
    mul : M → M → M
    assoc : ∀ f g h → mul (mul f g) h ≡ mul f (mul g h)
    left-id : ∀ f → mul unit f ≡ f
    right-id : ∀ f → mul f unit ≡ f
open Monoid public

record Action (A B : Set)
  (MA : Monoid A) (MB : Monoid B) : Set₁ where
  constructor action
  field
    act : B → A → A
    act-unit : ∀ a → act (Monoid.unit MB) a ≡ a
    act-unit-preserving : ∀ b → act b (Monoid.unit MA) ≡ Monoid.unit MA
    act-mul : ∀ b₁ b₂ a →
      act (Monoid.mul MB b₁ b₂) a ≡ act b₁ (act b₂ a)
    act-hom : ∀ b a₁ a₂ →
      act b (Monoid.mul MA a₁ a₂) ≡
      Monoid.mul MA (act b a₁) (act b a₂)
open Action public

record Semidirect (A B : Set) : Set₁ where
  constructor semidirect
  field
    leftMonoid : Monoid A
    rightMonoid : Monoid B
    leftAction : Action A B leftMonoid rightMonoid
open Semidirect public

semidirectMul :
  ∀ {A B : Set} → Semidirect A B → (A × B) → (A × B) → (A × B)
semidirectMul S (a , b) (a' , b') =
  Monoid.mul (leftMonoid S) a (Action.act (leftAction S) b a') ,
  Monoid.mul (rightMonoid S) b b'

-- A semidirect embedding is deliberately a transfer contract. The theorem
-- applies to the concrete recurrent carrier only after encode/decode and
-- one-step compatibility are supplied explicitly.
record SemidirectCycleEmbedding
  {A B : Set}
  (S : Semidirect A B)
  (X : Set) : Set₁ where
  constructor semidirectCycleEmbedding
  field
    encode : X → A × B
    decode : A × B → X
    decode-encode : ∀ x → decode (encode x) ≡ x
    carrierStep : A × B → A × B
    fixedElement : A × B
    carrierStep-law :
      ∀ p → carrierStep p ≡ semidirectMul S p fixedElement
    step : X → X
    step-law :
      ∀ x → decode (carrierStep (encode x)) ≡ step x
open SemidirectCycleEmbedding public
