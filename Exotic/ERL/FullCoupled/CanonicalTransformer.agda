{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalTransformer where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; _+_; _*_; _∸_)
open import Data.Nat.DivMod using (_/_)
open import Data.Nat.Properties using (_≤?_; yes; no)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8Add
  ; int8Mul
  ; int8OfNat
  ; zero8
  ; one8
  ; max8
  )
open import Exotic.ERL.FullCoupled.FiniteLearner using
  ( Token
  ; tokenCode
  )

------------------------------------------------------------------------
-- The canonical order is represented directly in the syntax of this file:
-- E -> RoPE -> Pyr^top-k -> Fastfood -> sR1 -> sR2 -> GateNN -> Pi.
-- Only the permutation stage is allowed to move coordinates.
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
  pair (observationCode t) (contextCode t)
  where
    observationCode : Token → Int8
    observationCode t =
      int8Add (tokenCode t) (reward t)

    contextCode : Token → Int8
    contextCode t =
      int8Add (previousAction t) (nextObservation t)

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
fastfood (pair x y) = pair
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
    mu3 sigma3 projection : Int8

open GateParameters public

gate : GateParameters → Pair → Pair
 gate gp (pair x y) =
  let epsilon = one8
      w3 = int8Add (mu3 gp) (int8Mul (sigma3 gp) epsilon)
      gx = int8Mul w3 x
      gy = int8Mul w3 y
  in pair gx gy

projection : Pair → Int8
projection (pair x y) = int8Add x y

canonicalForward : GateParameters → Token → Int8
canonicalForward gp t =
  projection (gate gp (sR2 (sR1 (fastfood (pyrTopK (rope (embedding t)))))))

canonicalOrder : ∀ (gp : GateParameters) (t : Token) →
  canonicalForward gp t ≡
  projection (gate gp (sR2 (sR1 (fastfood (pyrTopK (rope (embedding t)))))))
canonicalOrder gp t = refl

------------------------------------------------------------------------
-- The parameter-sensitive scalar gate is split into primal and local finite
-- pullback data.  This is the exact algebraic cotangent rule used by the
-- learner; no host-language autodiff participates.
------------------------------------------------------------------------

record GateVJP : Set where
  constructor gateVjp
  field
    primalGate : Int8
    gradMu : Int8
    gradSigma : Int8
    gradInput : Int8

open GateVJP public

gateScalarVJP : Int8 → Int8 → Int8 → GateVJP
gateScalarVJP mu sigma x =
  let w = int8Add mu (int8Mul sigma one8)
      y = int8Mul w x
      gm = x
      gs = x
      gx = w
  in gateVjp y gm gs gx

gateScalarVJPPrimal : ∀ (mu sigma x : Int8) →
  primalGate (gateScalarVJP mu sigma x) ≡
  int8Mul (int8Add mu (int8Mul sigma one8)) x
gateScalarVJPPrimal mu sigma x = refl

gateScalarVJPPullback : ∀ (mu sigma x c : Int8) →
  gradMu (gateScalarVJP mu sigma x) ≡ int8Mul c x
  
gateScalarVJPPullback mu sigma x c =
  refl

gateScalarVJPSigma : ∀ (mu sigma x c : Int8) →
  gradSigma (gateScalarVJP mu sigma x) ≡ int8Mul c x
 gateScalarVJPSigma mu sigma x c = refl

gateScalarVJPInput : ∀ (mu sigma x c : Int8) →
  gradInput (gateScalarVJP mu sigma x) ≡
  int8Mul c (int8Add mu (int8Mul sigma one8))
gateScalarVJPInput mu sigma x c = refl
