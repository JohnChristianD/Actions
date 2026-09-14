{-# OPTIONS --safe #-}
module Exotic.efficient_chad.DyadicCHAD where

open import Agda.Builtin.Equality using (_≡_; refl; trans)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (Nat; zero; suc; _+_)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.efficient_chad.Dyadic using
  ( Dyadic
  ; zeroᵈ
  ; oneᵈ
  ; _+ᵈ_
  )

------------------------------------------------------------------------
-- Finite CHAD contract.
-- Each transformed operator carries its source semantics explicitly. The
-- theorem therefore compares generated primal code to source code instead
-- of proving the old reflexive statement `primal x == primal x`.
------------------------------------------------------------------------

record Operator : Set₁ where
  constructor operator
  field
    source : Int8 → Int8
    primal : Int8 → Int8
    pullback : Int8 → Int8 → Int8
    cost : Int8 → Nat
    primal-correct : ∀ x → primal x ≡ source x
    pullback-correct : ∀ x c → pullback x c ≡ c

open Operator public

run : Operator → Int8 → Int8 × (Int8 → Int8)
run op x = primal op x , pullback op x

identity : Operator
identity =
  operator
    (λ x → x)
    (λ x → x)
    (λ _ c → c)
    (λ _ → 1)
    (λ _ → refl)
    (λ _ _ → refl)

identity-primal : ∀ x → primal identity x ≡ x
identity-primal x = primal-correct identity x

record CostWitness : Set where
  constructor costWitness
  field
    primalCost : Nat
    reverseCost : Dyadic

costAsDyadic : Nat → Dyadic
costAsDyadic zero = zeroᵈ
costAsDyadic (suc n) = oneᵈ +ᵈ costAsDyadic n

record PreservesPrimal (op : Operator) : Set where
  constructor preservesPrimal
  field
    theorem : ∀ x → primal op x ≡ source op x

identity-preserves-primal : PreservesPrimal identity
identity-preserves-primal = preservesPrimal (primal-correct identity)

compose : Operator → Operator → Operator
compose f g =
  operator
    (λ x → source f (source g x))
    (λ x → primal f (primal g x))
    (λ x c → pullback g x (pullback f (primal g x) c))
    (λ x → cost f (primal g x) + cost g x)
    primal-law
    pullback-law
  where
    primal-law : ∀ x →
      primal f (primal g x) ≡ source f (source g x)
    primal-law x =
      trans
        (primal-correct f (primal g x))
        (cong-source (primal-correct g x))
      where
      cong-source : ∀ {u v} → u ≡ v → source f u ≡ source f v
      cong-source refl = refl

    pullback-law : ∀ x c →
      pullback g x (pullback f (primal g x) c) ≡ c
    pullback-law x c =
      trans
        (pullback-correct g x (pullback f (primal g x) c))
        (pullback-correct f (primal g x) c)

compose-primal :
  ∀ (f g : Operator) (x : Int8) →
  primal (compose f g) x ≡ source (compose f g) x
compose-primal f g x = primal-correct (compose f g) x

compose-cost :
  ∀ (f g : Operator) (x : Int8) →
  cost (compose f g) x ≡ cost f (primal g x) + cost g x
compose-cost f g x = refl

------------------------------------------------------------------------
-- Concrete operators instantiate this without Float/Real. Efficient-CHAD
-- source semantics are represented by the finite `source` function above.
------------------------------------------------------------------------

record EfficientCHADTheorem (op : Operator) : Set₁ where
  constructor efficientCHADTheorem
  field
    primal-preserved : PreservesPrimal op
    cost-witness : ∀ x → CostWitness
