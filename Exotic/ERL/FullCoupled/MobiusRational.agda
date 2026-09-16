{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.MobiusRational where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import Agda.Builtin.Int as I
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (toℕ)
open import Data.Nat using (_∸_; _<ᵇ_)
open import Exotic.efficient_chad.Int8 using (Int8; code; int8OfNat)

record FiniteRational : Set where
  constructor finiteRational
  field
    numerator denominator : I.Int
open FiniteRational public

signedCode : Int8 → I.Int
signedCode x with toℕ (code x) <ᵇ 128
... | true = I.pos (toℕ (code x))
... | false = I.negsuc (255 ∸ toℕ (code x))

intAsRational : I.Int → FiniteRational
intAsRational n = finiteRational n (I.pos 1)

zeroR : FiniteRational
zeroR = intAsRational (I.pos 0)

identityRational : FiniteRational
identityRational = intAsRational (I.pos 1)

mobiusInt : I.Int → FiniteRational
mobiusInt (I.pos zero) = zeroR
mobiusInt (I.pos (suc zero)) = zeroR
mobiusInt (I.pos (suc (suc n))) =
  finiteRational (I.pos (suc (suc n))) (I.negsuc n)
mobiusInt (I.negsuc n) =
  finiteRational (I.negsuc n) (I.pos (suc (suc n)))

mobiusRatio8 : Int8 → FiniteRational
mobiusRatio8 x = mobiusInt (signedCode x)

mobiusRatio8-law : ∀ x → signedCode x ≢ I.pos 1 →
  mobiusRatio8 x ≡
    finiteRational (signedCode x)
      (I._-_ (I.pos 1) (signedCode x))
mobiusRatio8-law x neq with signedCode x
... | I.pos zero = refl
... | I.pos (suc zero) = λ q → neq q
... | I.pos (suc (suc n)) = refl
... | I.negsuc n = refl

mobiusSingularity : mobiusRatio8 (int8OfNat 1) ≡ zeroR
mobiusSingularity = refl
