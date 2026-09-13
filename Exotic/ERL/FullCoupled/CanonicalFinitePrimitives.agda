{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalFinitePrimitives where

open import Data.Fin as F using (Fin; toℕ)
open import Data.Nat using (ℕ; suc; _∸_)
open import Data.Nat.DivMod using (_/_)
open import Data.Nat.Properties using (_≤?_; yes; no)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8OfNat
  ; int8Add
  ; zero8
  )
open import Exotic.ERL.FullCoupled.CanonicalToken using
  ( Token
  ; observation
  ; previousAction
  ; reward
  ; nextObservation
  )

scaledMagnitude : Int8 → ℕ
scaledMagnitude x with toℕ (code x) ≤? 127
... | yes _ = toℕ (code x)
... | no _ = 256 ∸ toℕ (code x)

negEncode8 : ℕ → Int8
negEncode8 n = int8OfNat (256 ∸ n)

signReLU8 : Int8 → Int8
signReLU8 x with toℕ (code x) ≤? 127
... | yes _ = x
... | no _ = negEncode8 ((128 * scaledMagnitude x) / suc (scaledMagnitude x))

softsign8 : Int8 → Int8
softsign8 x with toℕ (code x) ≤? 127
... | yes _ = int8OfNat ((128 * toℕ (code x)) / suc (toℕ (code x)))
... | no _ = negEncode8 ((128 * scaledMagnitude x) / suc (scaledMagnitude x))

qε : ℕ → Int8 → Int8
qε tau x with scaledMagnitude x ≤? tau
... | yes _ = zero8
... | no _ = x

tokenCode : Token → Int8
tokenCode t = int8Add
  (int8Add (observation t) (previousAction t))
  (int8Add (reward t) (nextObservation t))
