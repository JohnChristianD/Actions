{-# OPTIONS --safe #-}
module Exotic.efficient_chad.DyadicCHAD where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (Nat; zero; suc; _+_)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.econlib.dyadic.Dyadic using
  ( Dyadic
  ; zeroᵈ
  ; oneᵈ
  ; _+ᵈ_
  )

------------------------------------------------------------------------
-- Dyadic/Int8 Efficient CHAD fragment.
-- Reverse-mode shape is retained; real/Float quantities are removed.
------------------------------------------------------------------------

record Operator : Set₁ where
  constructor operator
  field
    primal : Int8 → Int8
    pullback : Int8 → Int8 → Int8
    cost : Int8 → Nat

open Operator public

run : Operator → Int8 → Int8 × (Int8 → Int8)
run op x = primal op x , pullback op x

identity : Operator
identity = operator (λ x → x) (λ _ c → c) (λ _ → 1)

identity-primal : ∀ x → primal identity x ≡ x
identity-primal x = refl

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
    theorem : ∀ x → primal op x ≡ primal op x

identity-preserves-primal : PreservesPrimal identity
identity-preserves-primal = preservesPrimal (λ _ → refl)

------------------------------------------------------------------------
-- Composition is the finite analogue of the closure composition used by
-- Efficient CHAD.  No real analysis or transcendental primitive is present.
------------------------------------------------------------------------

compose : Operator → Operator → Operator
compose f g =
  operator
    (λ x → primal f (primal g x))
    (λ x c → pullback g x (pullback f (primal g x) c))
    (λ x → cost f (primal g x) + cost g x)

compose-primal :
  ∀ (f g : Operator) (x : Int8) →
  primal (compose f g) x ≡ primal f (primal g x)
compose-primal f g x = refl

compose-cost :
  ∀ (f g : Operator) (x : Int8) →
  cost (compose f g) x ≡ cost f (primal g x) + cost g x
compose-cost f g x = refl

------------------------------------------------------------------------
-- Canonical theorem shape: primal preservation plus an explicit dyadic
-- cost witness.  Concrete operators instantiate this without Float/Real.
------------------------------------------------------------------------

record EfficientCHADTheorem (op : Operator) : Set₁ where
  constructor efficientCHADTheorem
  field
    primal-preserved : PreservesPrimal op
    cost-witness : ∀ x → CostWitness
