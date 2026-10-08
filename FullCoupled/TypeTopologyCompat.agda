{-# OPTIONS --safe --without-K #-}

module FullCoupled.TypeTopologyCompat where

open import MLTT.Spartan public
open import MLTT.Athenian public
open import Unsafe.Haskell public
open import Naturals.Order public
open import Naturals.Addition public
open import Naturals.Multiplication public
open import Naturals.Properties public
open import Integers.Type public
open import Integers.Addition public
open import Integers.Multiplication public
open import Integers.Negation public
open import Integers.Order public

Nat : Set
Nat = ℕ

Int : Set
Int = ℤ

_+Int_ : Int → Int → Int
_+Int_ = _+_

_*Int_ : Int → Int → Int
_*Int_ = _*_

_≤Int_ : Int → Int → Set
_≤Int_ = _≤ℤ_

≤-antisym : (m n : Nat) → m ≤ n → n ≤ m → m ＝ n
≤-antisym = ≤-anti

n<1+n : (n : Nat) → n < succ n
n<1+n = ≤-succ
