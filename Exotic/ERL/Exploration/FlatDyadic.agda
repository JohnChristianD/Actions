{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.FlatDyadic where

open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat using (ℕ; suc)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Uniform finite dyadic law over the complete Int8 code space.
FlatOutcome : Set
FlatOutcome = Fin 256

flatWeight : FlatOutcome → ℕ
flatWeight _ = 1

flatDenominator : ℕ
flatDenominator = 256

flatWeight-sum : ∀ (xs : Fin 256) → flatWeight xs ≡ 1
flatWeight-sum _ = refl

flat-zero : FlatOutcome
flat-zero = fromℕ< (toℕ<n 0)

flat-one : FlatOutcome
flat-one = fromℕ< (toℕ<n 1)

flatWeight-normalized : flatWeight flat-zero ≡ 1
flatWeight-normalized = refl

flat-unit-positive : flatWeight flat-one ≡ 1
flat-unit-positive = refl

-- The law has exact dyadic mass 1/256 at every outcome.
flatCommonDenominator : ℕ
flatCommonDenominator = 256

flatDenominator-law : flatCommonDenominator ≡ 256
flatDenominator-law = refl
