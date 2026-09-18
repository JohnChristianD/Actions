{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SignedDivisibilityBridge where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Int using (Int)
open import Data.Integer.Divisibility.Signed using (_∣_; divides; ∣m∣n⇒∣m+n; ∣m⇒∣-m)

signedQuotient : Int → Int → Int → Set
signedQuotient q k z = z ≡ q * k

signedQuotient⇒divides :
  ∀ {q k z : Int} →
  signedQuotient q k z →
  k ∣ z
signedQuotient⇒divides {q} {k} {z} eq =
  divides q eq

divides-addition :
  ∀ {k x y : Int} →
  k ∣ x →
  k ∣ y →
  k ∣ x + y
divides-addition = ∣m∣n⇒∣m+n

divides-negation :
  ∀ {k x : Int} →
  k ∣ x →
  k ∣ - x
divides-negation = ∣m⇒∣-m

signedQuotient-refl :
  ∀ {q k : Int} →
  signedQuotient q k (q * k)
signedQuotient-refl = refl
