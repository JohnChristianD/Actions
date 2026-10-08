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

data ComparisonResult : Set where
  less equal greater : ComparisonResult

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

leIntBool : Int → Int → Bool
leIntBool x y with ℤ-trichotomous x y
... | inl _ = false
... | inr (inl _) = true
... | inr (inr _) = false

record Monad (M : Set → Set) : Set₁ where
  constructor monad
  field
    pure : {A : Set} → A → M A
    _>>=_ : {A B : Set} → M A → (A → M B) → M B

State : Set → Set → Set
State S A = S → A × S

listBind : {A B : Set} → List A → (A → List B) → List B
listBind [] f = []
listBind (x ∷ xs) f = f x ++ listBind xs f

listMonad : Monad List
listMonad = monad (λ x → x ∷ []) listBind

statePure : {S A : Set} → A → State S A
statePure x s = x , s

stateBind : {S A B : Set} → State S A → (A → State S B) → State S B
stateBind m k s =
  let x , s' = m s
  in k x s'

stateMonad : {S : Set} → Monad (State S)
stateMonad = monad statePure stateBind
