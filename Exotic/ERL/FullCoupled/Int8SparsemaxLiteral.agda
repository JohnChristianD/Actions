{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.Int8SparsemaxLiteral where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (toℕ)
open import Data.Nat using (_<ᵇ_)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; code; int8OfNat)

------------------------------------------------------------------------
-- Literal sparsemax on the integer score lattice.
--
-- Ordinary two-action sparsemax is the Tsallis-2/α=2 entmax map. When the
-- two scores are integer-valued, every nonzero score difference has magnitude
-- at least one, so the exact simplex solution is one-hot; equality gives the
-- unique half-half tie. No separate probabilistic or counterfactual model is
-- being introduced here.
------------------------------------------------------------------------

data TwoSupport : Set where
  leftOnly rightOnly both : TwoSupport

record Score2 : Set where
  constructor score2
  field left right : Int8
open Score2 public

support2 : Score2 → TwoSupport
support2 (score2 l r) with toℕ (code l) <ᵇ toℕ (code r)
... | true = rightOnly
... | false with toℕ (code r) <ᵇ toℕ (code l)
... | true = leftOnly
... | false = both

Weight2 : Set
Weight2 = Int8 × Int8

zeroQ7 halfQ7 oneQ7 : Int8
zeroQ7 = int8OfNat 0
halfQ7 = int8OfNat 64
oneQ7 = int8OfNat 128

sparsemax2 : Score2 → Weight2
sparsemax2 s with support2 s
... | leftOnly = oneQ7 , zeroQ7
... | rightOnly = zeroQ7 , oneQ7
... | both = halfQ7 , halfQ7

literal-left :
sparsemax2 (score2 (int8OfNat 2) (int8OfNat 1)) ≡
  (oneQ7 , zeroQ7)
literal-left = refl

literal-right :
sparsemax2 (score2 (int8OfNat 1) (int8OfNat 2)) ≡
  (zeroQ7 , oneQ7)
literal-right = refl

literal-tie :
sparsemax2 (score2 (int8OfNat 2) (int8OfNat 2)) ≡
  (halfQ7 , halfQ7)
literal-tie = refl
