{-# OPTIONS --safe #-}

module Exotic.ERL.Dyadic where

open import Data.Integer using (ℤ; +_; _+_; _-_; _*_; -_)
open import Data.Integer.Properties using (_≤?_; ≤-refl; ≤-trans)
open import Data.Nat using (ℕ; zero; suc; _^_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

record Dyadic : Set where
  constructor dyadic
  field
    numerator : ℤ
    exponent : ℕ

open Dyadic public

pow2 : ℕ → ℤ
pow2 zero = + 1
pow2 (suc n) = (+ 2) * pow2 n

zeroDyadic : Dyadic
zeroDyadic = dyadic (+ 0) zero

oneDyadic : Dyadic
oneDyadic = dyadic (+ 1) zero

negDyadic : Dyadic → Dyadic
negDyadic x = dyadic (- numerator x) (exponent x)

addDyadic : Dyadic → Dyadic → Dyadic
addDyadic x y = dyadic
  (numerator x * pow2 (exponent y) + numerator y * pow2 (exponent x))
  (exponent x + exponent y)

subDyadic : Dyadic → Dyadic → Dyadic
subDyadic x y = addDyadic x (negDyadic y)

mulDyadic : Dyadic → Dyadic → Dyadic
mulDyadic x y = dyadic
  (numerator x * numerator y)
  (exponent x + exponent y)

scalePow2 : ℕ → Dyadic → Dyadic
scalePow2 s x = dyadic (numerator x * pow2 s) (exponent x)

record 𝔻 (n B : ℕ) : Set where
  constructor bounded
  field
    k : ℤ
    lo : - (+ B) * (+ 2) ^ n ≤ k
    hi : k ≤ (+ B) * (+ 2) ^ n

open 𝔻 public

toDyadic : ∀ {n B} → 𝔻 n B → Dyadic
toDyadic {n} x = dyadic (k x) n

record Within {n B : ℕ} (v : ℤ) : Set where
  constructor within
  field
    loWitness : - (+ B) * (+ 2) ^ n ≤ v
    hiWitness : v ≤ (+ B) * (+ 2) ^ n

boundedPlus : ∀ {n B} → (x y : 𝔻 n B) → Within (k x + k y) → 𝔻 n B
boundedPlus x y witness =
  bounded
    (k x + k y)
    (Within.loWitness witness)
    (Within.hiWitness witness)

clampℤ : ℤ → ℤ → ℤ → ℤ
clampℤ lo hi x with x ≤? lo
... | yes _ = lo
... | no _ with hi ≤? x
... | yes _ = hi
... | no _ = x

record MomentumState : Set where
  constructor momentum
  field
    value : Dyadic

open MomentumState public

momentumEffective : MomentumState → Dyadic
momentumEffective = value

momentumStep : Dyadic → MomentumState → Dyadic → MomentumState
momentumStep beta state gradient =
  momentum
    (addDyadic
      (mulDyadic beta (momentumEffective state))
      (mulDyadic (subDyadic oneDyadic beta) gradient))

momentumStepEquation : ∀ beta state gradient →
  value (momentumStep beta state gradient)
    ≡ addDyadic
        (mulDyadic beta (momentumEffective state))
        (mulDyadic (subDyadic oneDyadic beta) gradient)
momentumStepEquation beta state gradient = refl

record Grid (n : ℕ) : Set where
  constructor grid
  field
    valueₙ : ℤ

open Grid public

record SparsePair (n : ℕ) : Set where
  constructor sparsePair
  field
    left right : Grid (suc n)

open SparsePair public

sparsemax2 : ∀ {n} → Grid n → Grid n → SparsePair n
sparsemax2 {n} a b = sparsePair (grid p) (grid (pow2 (suc n) - p))
  where
    raw : ℤ
    raw = valueₙ a - valueₙ b + pow2 n

    p : ℤ
    p = clampℤ (+ 0) (pow2 (suc n)) raw

momentumStep-is-definitional : ∀ beta state gradient →
  value (momentumStep beta state gradient)
    ≡ value (momentumStep beta state gradient)
momentumStep-is-definitional beta state gradient = refl

sparsemax2-is-definitional : ∀ {n} (a b : Grid n) →
  sparsemax2 a b ≡ sparsemax2 a b
sparsemax2-is-definitional a b = refl
