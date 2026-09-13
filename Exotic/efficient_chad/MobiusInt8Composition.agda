{-# OPTIONS --safe #-}
module Exotic.efficient_chad.MobiusInt8Composition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_)
open import Exotic.efficient_chad.Int8 using (Int8)

record FiniteMobiusAction : Set₁ where
  constructor mobiusAction
  field
    act : Int8 × Int8 → Int8 × Int8

open FiniteMobiusAction public

mobiusCompose : FiniteMobiusAction → FiniteMobiusAction → FiniteMobiusAction
mobiusCompose outer inner =
  mobiusAction (λ p → act outer (act inner p))

mobius-compose-law : ∀ (outer inner : FiniteMobiusAction) (p : Int8 × Int8)
  → act (mobiusCompose outer inner) p ≡ act outer (act inner p)
mobius-compose-law outer inner p = refl

-- This is the exact finite action-composition theorem needed by a certified
-- Möbius activation layer. A matrix/product witness for a particular action,
-- plus the unary projective/denominator law, is an additional activation
-- theorem and must be supplied by concrete Int8 semantics.
