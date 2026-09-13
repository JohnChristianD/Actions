{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.DyadicFastfood where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; int8Mul; zero8; one8; max8)
record DyadicDiagonal : Set where
 constructor diagonal
 field left right : Int8
signDiagonal : DyadicDiagonal
signDiagonal = diagonal one8 max8
applyDiagonal : DyadicDiagonal → Int8 × Int8 → Int8 × Int8
applyDiagonal d (x , y) = int8Mul (left d) x , int8Mul (right d) y
signDiagonal-neutral : applyDiagonal (diagonal one8 one8) (zero8 , zero8) ≡ zero8 , zero8
signDiagonal-neutral = refl
