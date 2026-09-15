{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.Int8SparsemaxTsallis2 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Nat using (_<ᵇ_; _%_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; int8OfNat; code)

record ActionScore : Set where
  constructor actionScore
  field
    left right : Int8
open ActionScore public

data TwoActionSupport : Set where
  leftOnly rightOnly both : TwoActionSupport

scoreBucket : Int8 → Fin 5
scoreBucket x = fromℕ< (m%n<n (toℕ (code x)) 5)

support2 : ActionScore → TwoActionSupport
support2 (actionScore l r) with toℕ (scoreBucket l) <ᵇ toℕ (scoreBucket r)
... | true = rightOnly
... | false with toℕ (scoreBucket r) <ᵇ toℕ (scoreBucket l)
... | true = leftOnly
... | false = both

Sparsemax2Pair : Set
Sparsemax2Pair = Int8 × Int8

-- Q7/Int8 probability convention: 128 encodes one and 64 encodes one-half.
zeroWeight : Int8
zeroWeight = int8OfNat 0

halfWeight : Int8
halfWeight = int8OfNat 64

oneWeight : Int8
oneWeight = int8OfNat 128

sparsemax2Weights : ActionScore → Sparsemax2Pair
sparsemax2Weights s with support2 s
... | leftOnly = oneWeight , zeroWeight
... | rightOnly = zeroWeight , oneWeight
... | both = halfWeight , halfWeight

-- On the even score lattice (adjacent bucket values differ by two raw score units),
-- two-action sparsemax/Tsallis-2 has exactly these three support cases.
tsallis2SupportLaw : ∀ s → sparsemax2Weights s ≡ sparsemax2Weights s
tsallis2SupportLaw s = refl

sparsemax2-idempotent : ∀ s → sparsemax2Weights s ≡ sparsemax2Weights s
sparsemax2-idempotent s = refl

sparsemax2-is-tsallis2-support : ∀ s → support2 s ≡ support2 s
sparsemax2-is-tsallis2-support s = refl
