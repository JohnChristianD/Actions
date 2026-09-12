{-# OPTIONS --safe #-}

module Exotic.ERL.Representation.Haar2 where

open import Agda.Builtin.Int using (Int)
open import Data.Integer.Base using (_+_; _-_; -_)
open import Data.Integer.Properties using
  (+-assoc; +-comm; +-identityʳ; +-inverseʳ; neg-distrib-+; neg-involutive)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; sym)
open import Relation.Binary.PropositionalEquality as Eq using (module ≡-Reasoning)

ℤ : Set
ℤ = Int

record HaarPair : Set where
  constructor haarPair
  field
    left right : ℤ

open HaarPair public

haar2 : HaarPair → HaarPair
haar2 p = haarPair
  (left p + right p)
  (left p - right p)

haar2-left-double : ∀ x y →
  left (haar2 (haarPair x y)) + right (haar2 (haarPair x y)) ≡ x + x
haar2-left-double x y = Eq.≡-Reasoning.begin
  (x + y) + (x - y)
  Eq.≡-Reasoning.≡⟨ sym (+-assoc x y (x - y)) ⟩
  x + (y + (x - y))
  Eq.≡-Reasoning.≡⟨ cong (λ z → x + z) (+-assoc y x (- y)) ⟩
  x + ((y + x) - y)
  Eq.≡-Reasoning.≡⟨ cong (λ z → x + z) (cong (λ z → z - y) (+-comm y x)) ⟩
  x + ((x + y) - y)
  Eq.≡-Reasoning.≡⟨ cong (λ z → x + z) (+-assoc x y (- y)) ⟩
  x + (x + (y - y))
  Eq.≡-Reasoning.≡⟨ cong (λ z → x + (x + z)) (+-inverseʳ y) ⟩
  x + (x + Data.Integer.Base.0ℤ)
  Eq.≡⟨ cong (λ z → x + z) (+-identityʳ x) ⟩
  x + x
  Eq.≡-Reasoning.∎

haar2-right-double : ∀ x y →
  left (haar2 (haarPair x y)) - right (haar2 (haarPair x y)) ≡ y + y
haar2-right-double x y = Eq.≡-Reasoning.begin
  (x + y) - (x - y)
  Eq.≡-Reasoning.≡⟨ sym (cong (λ z → (x + y) + z) (neg-distrib-+ x (- y))) ⟩
  (x + y) + ((- x) + (- (- y)))
  Eq.≡-Reasoning.≡⟨ cong (λ z → (x + y) + ((- x) + z)) (neg-involutive y) ⟩
  (x + y) + ((- x) + y)
  Eq.≡-Reasoning.≡⟨ +-assoc x y ((- x) + y) ⟩
  x + (y + ((- x) + y))
  Eq.≡-Reasoning.≡⟨ cong (λ z → x + z) (sym (+-assoc y (- x) y)) ⟩
  x + ((y + (- x)) + y)
  Eq.≡-Reasoning.≡⟨ cong (λ z → x + (z + y)) (+-comm y (- x)) ⟩
  x + ((- x + y) + y)
  Eq.≡-Reasoning.≡⟨ sym (+-assoc x (- x + y) y) ⟩
  (x + (- x + y)) + y
  Eq.≡⟨ cong (λ z → z + y) (sym (+-assoc x (- x) y)) ⟩
  (x + - x + y) + y
  Eq.≡⟨ cong (λ z → z + y) (cong (λ z → z + y) (+-inverseʳ x)) ⟩
  (Data.Integer.Base.0ℤ + y) + y
  Eq.≡⟨ cong (λ z → z + y) (+-identityʳ y) ⟩
  y + y
  Eq.≡-Reasoning.∎

haar2-square-scale : ∀ x y →
  haar2 (haar2 (haarPair x y)) ≡ haarPair (x + x) (y + y)
haar2-square-scale x y = cong₂ haarPair
  (haar2-left-double x y)
  (haar2-right-double x y)
