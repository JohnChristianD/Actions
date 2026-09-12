{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.AllSafeCombined_test where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; identityCHAD-law
  ; int8Roundtrip
  ; int8Add
  ; zero8
  ; int8IdentityAddLaw
  )

canonicalInt8Identity : ∀ (x : Int8) → identityCHAD-law x
canonicalInt8Identity x = identityCHAD-law x

canonicalInt8Roundtrip : ∀ (x : Int8) → int8Roundtrip x
canonicalInt8Roundtrip x = int8Roundtrip x

canonicalInt8AddIdentity : ∀ (x : Int8) → int8Add x zero8 ≡ x
canonicalInt8AddIdentity x = int8IdentityAddLaw x
