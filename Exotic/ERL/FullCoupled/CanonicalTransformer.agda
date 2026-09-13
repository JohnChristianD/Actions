{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalTransformer where

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
open import Exotic.ERL.Exploration.FiniteNoise using (Noise; zero)
open import Exotic.ERL.Exploration.NoisyNetFinite using (noiseDelta)
open import Exotic.ERL.FullCoupled.FiniteLearner using
  ( Token
  ; reward
  ; previousAction
  ; nextObservation
  ; tokenCode
  )

------------------------------------------------------------------------
-- Canonical finite Transformer instance:
-- E -> RoPE -> Pyr^top-k -> Fastfood -> sR1 -> sR2 -> GateNN -> Pi.
-- W = 2 is the finite 2-token proof instance of W = 2^q.
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

gateWeight : GateParameters → Noise → Int8
gateWeight gp epsilon =
  int8Add
    (mu3 gp)
    (int8Mul (sigma3 gp) (noiseDelta epsilon))

gate : GateParameters → Noise → Pair → Pair
gate gp epsilon (pair x y) =
  let w3 = gateWeight gp epsilon
  in pair
       (int8Mul w3 x)
       (int8Mul w3 y)

projection : GateParameters → Pair → Int8
projection gp (pair x y) =
  int8Mul (projectionScale gp) (int8Add x y)

canonicalRepresentation : GateParameters → Noise → Token → Pair
canonicalRepresentation gp epsilon t =
  sR2
    (sR1
      (fastfood
        (pyrTopK
          (rope
            (embedding t)))) )

canonicalForward : GateParameters → Noise → Token → Int8
canonicalForward gp epsilon t =
  projection gp
    (gate gp epsilon
      (canonicalRepresentation gp epsilon t))

canonicalOrder : ∀ (gp : GateParameters) (epsilon : Noise) (t : Token) →
  canonicalForward gp epsilon t ≡
  projection gp
    (gate gp epsilon
      (sR2
        (sR1
          (fastfood
            (pyrTopK
              (rope
                (embedding t)))))))
canonicalOrder gp epsilon t = refl

zeroNoiseWeight : ∀ (gp : GateParameters) →
  gateWeight gp zero ≡ mu3 gp
zeroNoiseWeight gp = refl

------------------------------------------------------------------------
-- Explicit finite VJP for the complete noisy gate/projection node.
-- This is a discrete cotangent transport contract, not a real-analysis claim.
------------------------------------------------------------------------

record GateVJP : Set where
  constructor gateVjp
  field
    primalGate : Int8
    gradMu gradSigma gradInput gradProjectionScale : Int8

open GateVJP public

gateVJP : GateParameters → Noise → Pair → GateVJP
gateVJP gp epsilon (pair x y) =
  let w = gateWeight gp epsilon
      inner = int8Add x y
      p = int8Mul (projectionScale gp) (int8Mul w inner)
      gateScale = int8Mul (projectionScale gp) inner
      inputScale = int8Mul (projectionScale gp) w
  in gateVjp
       p
       gateScale
       (int8Mul gateScale (noiseDelta epsilon))
       inputScale
       (int8Mul w inner)

gateVJPPrimal : ∀ (gp : GateParameters) (epsilon : Noise) (x y : Int8) →
  primalGate (gateVJP gp epsilon (pair x y)) ≡
  projection gp (gate gp epsilon (pair x y))
gateVJPPrimal gp epsilon x y = refl

gateVJPMu : ∀ (gp : GateParameters) (epsilon : Noise) (x y c : Int8) →
  gradMu (gateVJP gp epsilon (pair x y)) ≡
  int8Mul c (int8Mul (projectionScale gp) (int8Add x y))
gateVJPMu gp epsilon x y c = refl

gateVJPSigma : ∀ (gp : GateParameters) (epsilon : Noise) (x y c : Int8) →
  gradSigma (gateVJP gp epsilon (pair x y)) ≡
  int8Mul c
    (int8Mul
      (int8Mul (projectionScale gp) (int8Add x y))
      (noiseDelta epsilon))
gateVJPSigma gp epsilon x y c = refl

gateVJPInput : ∀ (gp : GateParameters) (epsilon : Noise) (x y c : Int8) →
  gradInput (gateVJP gp epsilon (pair x y)) ≡
  int8Mul c
    (int8Mul (projectionScale gp) (gateWeight gp epsilon))
gateVJPInput gp epsilon x y c = refl

gateVJPProjection : ∀ (gp : GateParameters) (epsilon : Noise) (x y c : Int8) →
  gradProjectionScale (gateVJP gp epsilon (pair x y)) ≡
  int8Mul c (int8Mul (gateWeight gp epsilon) (int8Add x y))
gateVJPProjection gp epsilon x y c = refl
