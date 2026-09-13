{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.DyadicFastfood where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; int8Add; zero8; one8; max8)

neg8 : Int8 → Int8
neg8 x = int8Add zero8 (int8Add max8 x)

record DyadicDiagonal : Set where
  constructor diagonal
  field
    left right : Int8

signDiagonal : DyadicDiagonal
signDiagonal = diagonal one8 max8

applyDiagonal : DyadicDiagonal → Int8 × Int8 → Int8 × Int8
applyDiagonal d (x , y) = int8Add (left d) x , int8Add (right d) y

signDiagonal-involution : ∀ p → applyDiagonal signDiagonal (applyDiagonal signDiagonal p) ≡ p
signDiagonal-involution (x , y) = refl

signDiagonal-neutral : applyDiagonal (diagonal one8 one8) (zero8 , zero8) ≡ zero8 , zero8
signDiagonal-neutral = refl

-- The canonical Fastfood Gaussian diagonal is replaced here only by the
-- dyadic sign diagonal; no Gaussian or transcendental scalar is introduced.
