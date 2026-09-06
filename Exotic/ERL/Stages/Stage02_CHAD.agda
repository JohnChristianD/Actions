{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage02_CHAD where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

record CHAD (A B : Set) : Set₁ where
  field
    primal : A → B
    pullback : A → B → A

idCHAD : ∀ {A : Set} → CHAD A A
idCHAD = record
  { primal = λ x → x
  ; pullback = λ x _ → x
  }

compose : ∀ {A B C : Set} → CHAD A B → CHAD B C → CHAD A C
compose f g = record
  { primal = λ x → CHAD.primal g (CHAD.primal f x)
  ; pullback = λ x dc → CHAD.pullback f x (CHAD.pullback g (CHAD.primal f x) dc)
  }

chadIdentity : ∀ {A : Set} (x : A) → CHAD.primal idCHAD x ≡ x
chadIdentity x = refl

natPlus : CHAD Nat Nat
natPlus = record
  { primal = λ x → x + suc zero
  ; pullback = λ x _ → x
  }
