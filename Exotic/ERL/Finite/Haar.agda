{-# OPTIONS --safe #-}

module Exotic.ERL.Finite.Haar where

open import Exotic.efficient_chad.Int8 using (Int8; int8Add; int8Mul; int8OfNat)
open import Exotic.ERL.Finite.Int8Vector using (Int8Vector4; vec4; x0; x1; x2; x3)

int8Sub : Int8 → Int8 → Int8
int8Sub x y = int8OfNat
  (256 + xNat ∸ yNat)
  where
  open import Data.Fin using (toℕ)
  open import Data.Nat using (_+_; _∸_)
  open import Exotic.efficient_chad.Int8 using (code)
  xNat = toℕ (code x)
  yNat = toℕ (code y)

addPair : Int8 → Int8 → Int8
addPair = int8Add

haar4 : Int8Vector4 → Int8Vector4
haar4 v = vec4
  (int8Add (int8Add (x0 v) (x1 v)) (int8Add (x2 v) (x3 v)))
  (int8Sub
    (int8Add (x0 v) (x1 v))
    (int8Add (x2 v) (x3 v)))
  (int8Sub (x0 v) (x1 v))
  (int8Sub (x2 v) (x3 v))

haar4Linear : Int8Vector4 → Int8Vector4 → Int8Vector4
haar4Linear a b = haar4 (vec4
  (int8Add (x0 a) (x0 b))
  (int8Add (x1 a) (x1 b))
  (int8Add (x2 a) (x2 b))
  (int8Add (x3 a) (x3 b)))
