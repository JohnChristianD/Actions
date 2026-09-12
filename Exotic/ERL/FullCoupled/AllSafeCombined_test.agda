{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.AllSafeCombined_test where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; identityCHAD-law
  ; int8Roundtrip
  )

canonicalInt8Identity : ∀ (x : Int8) → identityCHAD-law x
canonicalInt8Identity x = identityCHAD-law x

canonicalInt8Roundtrip : ∀ (x : Int8) → int8Roundtrip x
canonicalInt8Roundtrip x = int8Roundtrip x
