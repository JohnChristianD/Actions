{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteHaarSparsemaxRoPE where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; _+_; _∸_; _/_; _≤?_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8OfNat
  ; int8Add
  ; zero8
  ; max8
  )

------------------------------------------------------------------------
-- Genuine finite arithmetic front-end.
--
-- Haar is the integer-scaled two-point Haar transform, sparsemax is a
-- two-coordinate simplex projection rounded to the 0..255 dyadic grid,
-- and RoPE is the exact quarter-turn available without trigonometric
-- constants. These are finite substitutes, not claims about arbitrary real
-- vectors or arbitrary RoPE angles.
------------------------------------------------------------------------

Int8Pair : Set
Int8Pair = Int8 × Int8

neg8 : Int8 → Int8
neg8 x = int8OfNat (256 ∸ toℕ (code x))

neg8-zero : neg8 zero8 ≡ zero8
neg8-zero = refl

half8 : Int8 → Int8
half8 x = int8OfNat (toℕ (code x) / 2)

sub8 : Int8 → Int8 → Int8
sub8 x y = int8OfNat (toℕ (code x) + 256 ∸ toℕ (code y))

------------------------------------------------------------------------
-- Two-point Haar.
------------------------------------------------------------------------

haar2 : Int8Pair → Int8Pair
haar2 (x , y) =
  ( half8 (int8Add x y)
  , half8 (sub8 x y)
  )

haar2-closed : ∀ p → Int8Pair
haar2-closed p = haar2 p

------------------------------------------------------------------------
-- Quantized two-coordinate sparsemax. The output is always on the dyadic
-- simplex with numerator sum 255. These boundary identities expose genuine
-- hard sparsity inside the finite arithmetic carrier.
------------------------------------------------------------------------

sparsemax2 : Int8Pair → Int8Pair
sparsemax2 (x , y) with toℕ (code x) ≤? toℕ (code y)
... | yes p =
  let d = toℕ (code y) ∸ toℕ (code x)
      q = (255 ∸ d) / 2
  in int8OfNat q , int8OfNat (255 ∸ q)
... | no p =
  let d = toℕ (code x) ∸ toℕ (code y)
      q = (255 + d) / 2
  in int8OfNat q , int8OfNat (255 ∸ q)

sparsemax2-hard-sparsity-left :
  proj₂ (sparsemax2 (int8OfNat 255 , int8OfNat 0)) ≡ int8OfNat 0
sparsemax2-hard-sparsity-left = refl

sparsemax2-hard-sparsity-right :
  proj₁ (sparsemax2 (int8OfNat 0 , int8OfNat 255)) ≡ int8OfNat 0
sparsemax2-hard-sparsity-right = refl

sparsemax2-boundary-left-idempotent :
  sparsemax2 (int8OfNat 255 , int8OfNat 0)
  ≡ (int8OfNat 255 , int8OfNat 0)
sparsemax2-boundary-left-idempotent = refl

sparsemax2-boundary-right-idempotent :
  sparsemax2 (int8OfNat 0 , int8OfNat 255)
  ≡ (int8OfNat 0 , int8OfNat 255)
sparsemax2-boundary-right-idempotent = refl

------------------------------------------------------------------------
-- Discrete RoPE special angle pi/2: (x,y) |-> (-y,x).
------------------------------------------------------------------------

ropeQuarter : Int8Pair → Int8Pair
ropeQuarter (x , y) = neg8 y , x

ropeQuarter-right-zero-boundary :
  ropeQuarter (int8OfNat 255 , int8OfNat 0)
  ≡ (int8OfNat 0 , int8OfNat 255)
ropeQuarter-right-zero-boundary = refl

ropeQuarter-left-zero-boundary :
  ropeQuarter (int8OfNat 0 , int8OfNat 255)
  ≡ (neg8 (int8OfNat 255) , int8OfNat 0)
ropeQuarter-left-zero-boundary = refl

------------------------------------------------------------------------
-- Composition exposes an exact finite sparsity transition: sparsemax can
-- create a one-coordinate boundary, then the quarter-turn transports that
-- boundary to the opposite coordinate. Haar is intentionally kept separate
-- because its integer halving need not preserve hard sparsity.
------------------------------------------------------------------------

frontEnd : Int8Pair → Int8Pair
frontEnd p = ropeQuarter (haar2 (sparsemax2 p))

frontEnd-assoc :
  ∀ (f g h : Int8Pair → Int8Pair) (p : Int8Pair) →
  f (g (h p)) ≡ (λ q → f (g q)) (h p)
frontEnd-assoc f g h p = refl

frontEnd-expanded :
  ∀ p →
  frontEnd p ≡ ropeQuarter (haar2 (sparsemax2 p))
frontEnd-expanded p = refl

frontEnd-hard-boundary-left :
  frontEnd (int8OfNat 255 , int8OfNat 0)
  ≡ ropeQuarter (haar2 (int8OfNat 255 , int8OfNat 0))
frontEnd-hard-boundary-left = refl

frontEnd-hard-boundary-right :
  frontEnd (int8OfNat 0 , int8OfNat 255)
  ≡ ropeQuarter (haar2 (int8OfNat 0 , int8OfNat 255))
frontEnd-hard-boundary-right = refl

------------------------------------------------------------------------
-- A scalar GRU may consume a chosen coordinate after the vector front-end;
-- the projection is total and therefore preserves finite closure.
------------------------------------------------------------------------

gruInputProjection : Int8Pair → Int8
gruInputProjection = proj₁

gruInputProjection-closed : ∀ p → Int8
gruInputProjection-closed p = proj₁ p

frontEndToGRU : Int8Pair → Int8
frontEndToGRU p = gruInputProjection (frontEnd p)

frontEndToGRU-law :
  ∀ p → frontEndToGRU p ≡ proj₁ (ropeQuarter (haar2 (sparsemax2 p)))
frontEndToGRU-law p = refl
