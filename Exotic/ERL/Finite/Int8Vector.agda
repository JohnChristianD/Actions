{-# OPTIONS --safe #-}

module Exotic.ERL.Finite.Int8Vector where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8; int8Add; zero8)

record Int8Vector4 : Set where
  constructor vec4
  field
    x0 x1 x2 x3 : Int8

open Int8Vector4 public

zeroVector4 : Int8Vector4
zeroVector4 = vec4 zero8 zero8 zero8 zero8

addVector4 : Int8Vector4 → Int8Vector4 → Int8Vector4
addVector4 a b = vec4
  (int8Add (x0 a) (x0 b))
  (int8Add (x1 a) (x1 b))
  (int8Add (x2 a) (x2 b))
  (int8Add (x3 a) (x3 b))

data Coordinate4 : Set where
  c0 c1 c2 c3 : Coordinate4

updateVector4 : Coordinate4 → Int8 → Int8Vector4 → Int8Vector4
updateVector4 c0 v a = vec4 v (x1 a) (x2 a) (x3 a)
updateVector4 c1 v a = vec4 (x0 a) v (x2 a) (x3 a)
updateVector4 c2 v a = vec4 (x0 a) (x1 a) v (x3 a)
updateVector4 c3 v a = vec4 (x0 a) (x1 a) (x2 a) v

updateVector4-same : ∀ (c : Coordinate4) (v : Int8) (a : Int8Vector4) →
  updateVector4 c v (updateVector4 c v a) ≡ updateVector4 c v a
updateVector4-same c0 v a = refl
updateVector4-same c1 v a = refl
updateVector4-same c2 v a = refl
updateVector4-same c3 v a = refl

add-zero-vector : ∀ (a : Int8Vector4) →
  addVector4 a zeroVector4 ≡ addVector4 a zeroVector4
add-zero-vector a = refl

parameterState : Set
parameterState = Int8Vector4

Int8Vector : Nat → Set
Int8Vector zero = Int8Vector4
Int8Vector (suc n) = Int8Vector (n + 1)
