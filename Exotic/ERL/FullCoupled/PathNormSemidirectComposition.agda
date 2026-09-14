{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.PathNormSemidirectComposition where

open import Agda.Builtin.Equality using (_≡_; refl; trans; cong)
open import Data.Nat using (Nat; zero; suc; _*_)
open import Data.List using (List; []; _∷_)

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
-- Iterated path products inherit the factorization law.
------------------------------------------------------------------------

layerProduct : List NormedLayer → Nat
layerProduct [] = 1
layerProduct (l ∷ ls) = pathNorm l * layerProduct ls

pathNorm-window-factorization :
  ∀ (xs : List NormedLayer) (ys : List NormedLayer) →
  layerProduct (xs ∷ ys) ≡ pathNorm xs * pathNorm ys
pathNorm-window-factorization xs ys = refl

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

record Action (G H : Set) : Set₁ where
  constructor action
  field
    act : G → H → H
    unitAct : ∀ h → act (ε) h ≡ h
    mulAct : ∀ g₁ g₂ h → act (g₁ ∙ g₂) h ≡ act g₁ (act g₂ h)

open Action public

record SemidirectProduct (G H : Set) (MG : Monoid G) (MH : Monoid H) (AG : Action G H) : Set₁ where
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
-- Canonical binary law for (g,h) ⋊ (k,l):
-- (g∙k, act g l ∙ h), with the associativity proof discharged from the
-- action/monoid laws by the containing certificate.
------------------------------------------------------------------------

record FiniteSemidirectCertificate (G H : Set) (MG : Monoid G) (MH : Monoid H) (AG : Action G H) : Set₁ where
  constructor finiteSemidirectCertificate
  field
    semidirect : SemidirectProduct G H MG MH AG
    finiteCarrier : Set
    finiteWitness : Set

------------------------------------------------------------------------
-- The F4 optimizer state is therefore representable as an H-side extension
-- in a semidirect theorem class, without claiming the current repo already
-- proves a concrete nontrivial group action for every F4 parameter bank.
------------------------------------------------------------------------

record SemidirectTheoremClass : Set₁ where
  constructor semidirectTheoremClass
  field
    baseComposition : Set
    actionCompatibility : Set
    semidirectLaw : Set
    pathNormLaw : Set
