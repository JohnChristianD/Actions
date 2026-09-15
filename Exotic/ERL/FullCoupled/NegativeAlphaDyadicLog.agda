{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.NegativeAlphaDyadicLog where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8OfNat
  ; int8Mul
  ; max8
  ; zero8
  )

negativeAlpha8 : Int8
negativeAlpha8 = int8OfNat 255

pow2Dyadic : Fin 8 → Int8
pow2Dyadic zero = int8OfNat 1
pow2Dyadic (suc zero) = int8OfNat 2
pow2Dyadic (suc (suc zero)) = int8OfNat 4
pow2Dyadic (suc (suc (suc zero))) = int8OfNat 8
pow2Dyadic (suc (suc (suc (suc zero)))) = int8OfNat 16
pow2Dyadic (suc (suc (suc (suc (suc zero))))) = int8OfNat 32
pow2Dyadic (suc (suc (suc (suc (suc (suc zero)))))) = int8OfNat 64
pow2Dyadic (suc (suc (suc (suc (suc (suc (suc zero))))))) = int8OfNat 128

logExponent : Fin 8 → Nat
logExponent zero = 0
logExponent (suc zero) = 1
logExponent (suc (suc zero)) = 2
logExponent (suc (suc (suc zero))) = 3
logExponent (suc (suc (suc (suc zero)))) = 4
logExponent (suc (suc (suc (suc (suc zero))))) = 5
logExponent (suc (suc (suc (suc (suc (suc zero)))))) = 6
logExponent (suc (suc (suc (suc (suc (suc (suc zero))))))) = 7

pow2Nat : Nat → Nat
pow2Nat zero = 1
pow2Nat (suc n) = 2 * pow2Nat n

toNat : Int8 → Nat
toNat x = toℕ (Exotic.efficient_chad.Int8.Int8.code x)

dyadicExponentLaw :
  ∀ k → pow2Nat (logExponent k) ≡ toNat (pow2Dyadic k)
dyadicExponentLaw zero = refl
dyadicExponentLaw (suc zero) = refl
dyadicExponentLaw (suc (suc zero)) = refl
dyadicExponentLaw (suc (suc (suc zero))) = refl
dyadicExponentLaw (suc (suc (suc (suc zero)))) = refl
dyadicExponentLaw (suc (suc (suc (suc (suc zero))))) = refl
dyadicExponentLaw (suc (suc (suc (suc (suc (suc zero)))))) = refl
dyadicExponentLaw (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl

log2Dyadic : Fin 8 → Int8
log2Dyadic k = int8OfNat (logExponent k)

negativeAlphaBonus : Fin 8 → Int8
negativeAlphaBonus k = int8Mul negativeAlpha8 (log2Dyadic k)

negativeAlphaDyadicLogLaw : ∀ k → negativeAlphaBonus k ≡ negativeAlphaBonus k
negativeAlphaDyadicLogLaw k = refl

optimisticInit : Int8
optimisticInit = max8

pessimisticInit : Int8
pessimisticInit = zero8

positiveLogDefaultInit : Int8
positiveLogDefaultInit = optimisticInit

negativeLogDefaultInit : Int8
negativeLogDefaultInit = pessimisticInit
