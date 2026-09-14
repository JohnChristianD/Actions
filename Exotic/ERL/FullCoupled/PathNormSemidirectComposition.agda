{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.PathNormSemidirectComposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (Nat; _*_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_)

------------------------------------------------------------------------
-- Finite path-norm factorization.
-- The normed-layer law is an explicit hypothesis, allowing exact Nat-only
-- factorization without importing reals, floats, or unrestricted division.
------------------------------------------------------------------------

record NormedLayer : Set₁ where
  constructor normedLayer
  field
    apply : Nat → Nat
    pathNorm : Nat

open NormedLayer public

record NormedComposition : Set₁ where
  constructor normedComposition
  field
    left right : NormedLayer
    composite : NormedLayer
    factorLaw : pathNorm composite ≡ pathNorm left * pathNorm right

open NormedComposition public

pathNorm-factorization :
  ∀ (C : NormedComposition) →
  pathNorm (composite C) ≡ pathNorm (left C) * pathNorm (right C)
pathNorm-factorization C = factorLaw C

------------------------------------------------------------------------
-- Iterated path products inherit factorization exactly at the list level.
------------------------------------------------------------------------

layerProduct : List NormedLayer → Nat
layerProduct [] = 1
layerProduct (l ∷ ls) = pathNorm l * layerProduct ls

layerProduct-append :
  ∀ xs ys →
  layerProduct (xs ++ ys) ≡ layerProduct xs * layerProduct ys
layerProduct-append [] ys = refl
layerProduct-append (x ∷ xs) ys = refl

------------------------------------------------------------------------
-- Finite semidirect-product contract.
-- G is the operator/group-like component and H is the optimizer/state
-- component acted on by G. The action laws are explicit.
------------------------------------------------------------------------

record Monoid (G : Set) : Set₁ where
  constructor monoid
  field
    ε : G
    _∙_ : G → G → G
    assoc : ∀ a b c → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)
    leftId : ∀ a → ε ∙ a ≡ a
    rightId : ∀ a → a ∙ ε ≡ a

open Monoid public

record Action (G H : Set) (MG : Monoid G) : Set₁ where
  constructor action
  field
    act : G → H → H
    unitAct : ∀ h → act (ε MG) h ≡ h
    mulAct : ∀ g₁ g₂ h →
      act ((_∙_ MG) g₁ g₂) h ≡ act g₁ (act g₂ h)

open Action public

record SemidirectProduct
  (G H : Set)
  (MG : Monoid G)
  (MH : Monoid H)
  (AG : Action G H MG) : Set₁ where
  constructor semidirectProduct
  field
    pair : Set
    pairDefinition : pair ≡ (G × H)
    multiply : pair → pair → pair
    identity : pair
    associativity : ∀ x y z → multiply (multiply x y) z ≡ multiply x (multiply y z)
    leftIdentity : ∀ x → multiply identity x ≡ x
    rightIdentity : ∀ x → multiply x identity ≡ x

open SemidirectProduct public

------------------------------------------------------------------------
-- A finite semidirect theorem class records the finite carrier witness
-- separately from the algebraic law. This avoids claiming that the current
-- F4 carrier is already a nontrivial group when it is presently a dyadic
-- arithmetic state space.
------------------------------------------------------------------------

record FiniteSemidirectCertificate
  (G H : Set)
  (MG : Monoid G)
  (MH : Monoid H)
  (AG : Action G H MG) : Set₁ where
  constructor finiteSemidirectCertificate
  field
    semidirect : SemidirectProduct G H MG MH AG
    finiteCarrier : List (G × H)

record SemidirectTheoremClass : Set₁ where
  constructor semidirectTheoremClass
  field
    baseComposition : Set
    actionCompatibility : Set
    semidirectLaw : Set
    pathNormLaw : Set
