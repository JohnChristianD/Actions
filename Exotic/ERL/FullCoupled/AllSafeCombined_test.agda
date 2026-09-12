{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.AllSafeCombined_test where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (toℕ)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8OfNat
  ; primal
  ; identityCHAD
  ; identityCHAD-law
  ; int8Roundtrip
  )

canonicalInt8Identity : ∀ (x : Int8) → primal identityCHAD x ≡ x
canonicalInt8Identity x = identityCHAD-law x

canonicalInt8Roundtrip : ∀ (x : Int8) →
  toℕ (code (int8OfNat (toℕ (code x)))) ≡ toℕ (code x)
canonicalInt8Roundtrip x = int8Roundtrip x
