{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalTransformer where

open import Agda.Builtin.Nat using (zero; suc)
open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; _∸_)
open import Data.Nat.Properties using (_≤?_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8Add
  ; int8Mul
  ; int8OfNat
  ; one8
  ; max8
  )
open import Exotic.ERL.FullCoupled.FiniteLearner using
  ( Token
  ; observation
  ; previousAction
  ; reward
  ; nextObservation
  ; tokenCode
  )

------------------------------------------------------------------------
-- Canonical order:
-- E -> RoPE -> Pyr^top-k -> Fastfood -> sR1 -> sR2 -> GateNN -> Pi.
-- The stages are deliberately named and nested in this order.
------------------------------------------------------------------------

record Pair : Set where
  constructor pair
  field
    left right : Int8

open Pair public

negate8 : Int8 → Int8
negate8 x = int8OfNat (256 ∸ toℕ (code x))

embedding : Token → Pair
embedding t =
  pair
    (int8Add (tokenCode t) (reward t))
    (int8Add (previousAction t) (nextObservation t))

rope : Pair → Pair
rope (pair x y) = pair y (negate8 x)

absNat : Int8 → ℕ
absNat x with toℕ (code x) ≤? 127
... | yes _ = toℕ (code x)
... | no _ = 256 ∸ toℕ (code x)

pyrTopK : Pair → Pair
pyrTopK (pair x y) with absNat x ≤? absNat y
... | yes _ = pair y x
... | no _ = pair x y

fastfood : Pair → Pair
fastfood (pair x y) =
  pair
    (int8Add x y)
    (int8Add x (negate8 y))

sR1 : Pair → Pair
sR1 (pair x y) = pair (signed x) (signed y)
  where
    signed : Int8 → Int8
    signed z with toℕ (code z) ≤? 127
    ... | yes _ = z
    ... | no _ = max8

sR2 : Pair → Pair
sR2 (pair x y) = pair
  (int8Mul x x)
  (int8Mul y y)

record GateParameters : Set where
  constructor gateParameters
  field
    mu3 sigma3 projectionScale : Int8

open GateParameters public

gate : GateParameters → Pair → Pair
gate gp (pair x y) =
  let epsilon = one8
      w3 = int8Add (mu3 gp) (int8Mul (sigma3 gp) epsilon)
  in pair (int8Mul w3 x) (int8Mul w3 y)

projection : Pair → Int8
projection (pair x y) = int8Add x y

canonicalForward : GateParameters → Token → Int8
canonicalForward gp t =
  projection
    (gate gp
      (sR2
        (sR1
          (fastfood
            (pyrTopK
              (rope
                (embedding t)))))))

canonicalOrder : ∀ (gp : GateParameters) (t : Token) →
  canonicalForward gp t ≡
  projection
    (gate gp
      (sR2
        (sR1
          (fastfood
            (pyrTopK
              (rope
                (embedding t)))))))
canonicalOrder gp t = refl

------------------------------------------------------------------------
-- Exact local finite VJP for the noisy gate.  The pullback functions consume
-- an output cotangent; they are not inferred by an external AD system.
------------------------------------------------------------------------

record GateVJP : Set where
  constructor gateVjp
  field
    primalGate : Int8
    gradMu gradSigma gradInput : Int8 → Int8

open GateVJP public

gateScalarVJP : Int8 → Int8 → Int8 → GateVJP
gateScalarVJP mu sigma x =
  let w = int8Add mu (int8Mul sigma one8)
  in gateVjp
       (int8Mul w x)
       (λ c → int8Mul c x)
       (λ c → int8Mul c x)
       (λ c → int8Mul c w)

gateScalarVJPPrimal : ∀ (mu sigma x : Int8) →
  primalGate (gateScalarVJP mu sigma x) ≡
  int8Mul (int8Add mu (int8Mul sigma one8)) x
gateScalarVJPPrimal mu sigma x = refl

gateScalarVJPPullback : ∀ (mu sigma x c : Int8) →
  gradMu (gateScalarVJP mu sigma x) c ≡ int8Mul c x
gateScalarVJPPullback mu sigma x c = refl

gateScalarVJPSigma : ∀ (mu sigma x c : Int8) →
  gradSigma (gateScalarVJP mu sigma x) c ≡ int8Mul c x
gateScalarVJPSigma mu sigma x c = refl

gateScalarVJPInput : ∀ (mu sigma x c : Int8) →
  gradInput (gateScalarVJP mu sigma x) c ≡
  int8Mul c (int8Add mu (int8Mul sigma one8))
gateScalarVJPInput mu sigma x c = refl
