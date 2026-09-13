{-# OPTIONS --safe #-}
module Exotic.efficient_chad.MobiusInt8Composition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; int8Add; int8Mul)

record FiniteMobiusMatrix : Set where
  constructor mobiusMatrix
  field
    a b c d : Int8

open FiniteMobiusMatrix public

mobiusAction : FiniteMobiusMatrix → Int8 × Int8 → Int8 × Int8
mobiusAction m p =
  ( int8Add (int8Mul (a m) (proj₁ p)) (int8Mul (b m) (proj₂ p))
  , int8Add (int8Mul (c m) (proj₁ p)) (int8Mul (d m) (proj₂ p))
  )

mobiusCompose : FiniteMobiusMatrix → FiniteMobiusMatrix → FiniteMobiusMatrix
mobiusCompose outer inner =
  mobiusMatrix
    (int8Add (int8Mul (a outer) (a inner)) (int8Mul (b outer) (c inner)))
    (int8Add (int8Mul (a outer) (b inner)) (int8Mul (b outer) (d inner)))
    (int8Add (int8Mul (c outer) (a inner)) (int8Mul (d outer) (c inner)))
    (int8Add (int8Mul (c outer) (b inner)) (int8Mul (d outer) (d inner)))

mobius-compose-law : ∀ (outer inner : FiniteMobiusMatrix) (p : Int8 × Int8)
  → mobiusAction (mobiusCompose outer inner) p
    ≡ mobiusAction outer (mobiusAction inner p)
mobius-compose-law outer inner p = refl

-- This is the finite homogeneous-coordinate Möbius composition theorem.
-- An activation-specific unary Möbius theorem additionally needs a checked
-- projective-coordinate/denominator interpretation; the generic CHAD layer
-- does not invent that interpretation for signReLU8 or softsign8.
