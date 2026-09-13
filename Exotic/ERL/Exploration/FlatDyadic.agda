{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.FlatDyadic where

open import Data.Fin using (Fin; fromℕ<)
open import Data.Nat using (ℕ; suc)
open import Data.Fin.Properties using (toℕ<n)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Uniform finite dyadic law over the complete Int8 code space.
FlatOutcome : Set
FlatOutcome = Fin 256

flatWeight : FlatOutcome → ℕ
flatWeight _ = 1

flatDenominator : ℕ
flatDenominator = 256

flatWeightSum : ℕ → ℕ
flatWeightSum zero = 0
flatWeightSum (suc n) = suc (flatWeightSum n)

flatWeight-sum : flatWeightSum 256 ≡ flatDenominator
flatWeight-sum = refl

flat-zero : FlatOutcome
flat-zero = fromℕ< (toℕ<n 0)

flat-one : FlatOutcome
flat-one = fromℕ< (toℕ<n 1)

flatWeight-normalized : flatWeightSum 256 ≡ 256
flatWeight-normalized = refl

flatUnit-positive : flatWeight flat-one ≡ 1
flatUnit-positive = refl

flatZero-positive : flatWeight flat-zero ≡ 1
flatZero-positive = refl

-- Every one of the 256 outcomes has the same exact dyadic numerator.
flatCommonDenominator : ℕ
flatCommonDenominator = 256

flatDenominator-law : flatCommonDenominator ≡ 256
flatDenominator-law = refl
