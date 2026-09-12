{-# OPTIONS --safe #-}

module Exotic.efficient_chad.Int8 where

import Data.Fin as F
open F using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat using (ℕ; suc; _+_; _*_) 
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

record Int8 : Set where
  constructor int8
  field
    code : Fin 256

open Int8 public

zero8 : Int8
zero8 = int8 F.zero

one8 : Int8
one8 = int8 (F.suc F.zero)

maxFin : ∀ {n : ℕ} → Fin (suc n)
maxFin {n = zero} = F.zero
maxFin {n = suc n} = F.suc (maxFin {n = n})

max8 : Int8
max8 = int8 maxFin

int8OfNat : ℕ → Int8
int8OfNat n = int8 (fromℕ< (m%n<n n 256))

int8Add : Int8 → Int8 → Int8
int8Add x y = int8OfNat (toℕ (code x) + toℕ (code y))

int8Mul : Int8 → Int8 → Int8
int8Mul x y = int8OfNat (toℕ (code x) * toℕ (code y))

record CHADOperator : Set₁ where
  constructor chadOperator
  field
    primal : Int8 → Int8
    pullback : Int8 → Int8 → Int8

open CHADOperator public

identityCHAD : CHADOperator
identityCHAD = chadOperator
  (λ x → x)
  (λ x cotangent → cotangent)

runCHAD : CHADOperator → Int8 → Int8 × (Int8 → Int8)
runCHAD op x = primal op x , pullback op x

identityCHAD-law : ∀ x → primal identityCHAD x ≡ x
identityCHAD-law x = refl

record AffineCHAD : Set₁ where
  constructor affineCHAD
  field
    scale bias : Int8

open AffineCHAD public

forwardAffine : AffineCHAD → Int8 → Int8
forwardAffine op x = int8Add (int8Mul (scale op) x) (bias op)

reverseAffine : AffineCHAD → Int8 → Int8 → Int8
reverseAffine op x cotangent = int8Mul (scale op) cotangent

affineCHADOperator : AffineCHAD → CHADOperator
affineCHADOperator op = chadOperator
  (forwardAffine op)
  (reverseAffine op)

record Int8SparsePair : Set where
  constructor int8SparsePair
  field
    left right : Int8

int8Sparsemax2 : Int8 → Int8 → Int8SparsePair
int8Sparsemax2 a b = int8SparsePair a b

int8Roundtrip : ∀ x → toℕ (code (int8OfNat (toℕ (code x)))) ≡ toℕ (code x)
int8Roundtrip x = trans
  (toℕ-fromℕ< (m%n<n (toℕ (code x)) 256))
  (m<n⇒m%n≡m (toℕ<n (code x)))
