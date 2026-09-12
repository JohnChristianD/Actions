{-# OPTIONS --safe #-}

module Exotic.ERL.Representation.HaarInt8 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (toℕ)
open import Data.Nat using (_∸_)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8Add
  ; int8OfNat
  ; code
  )

negate8 : Int8 → Int8
negate8 x = int8OfNat (256 ∸ toℕ (code x))

H8 : Int8 × Int8 → Int8 × Int8
H8 (x , y) = int8Add x y , int8Add x (negate8 y)

double8 : Int8 → Int8
double8 x = int8Add x x

H8-square : ∀ x y → H8 (H8 (x , y)) ≡ (double8 x , double8 y)
H8-square x y = refl
