{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.FlatDyadic where

open import Data.Fin using (Fin; fromℕ<)
open import Data.Nat using (ℕ; suc)
open import Data.Fin.Properties using (toℕ<n)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

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

flat-minus-one : FlatOutcome
flat-minus-one = fromℕ< (toℕ<n 255)

flat-two : FlatOutcome
flat-two = fromℕ< (toℕ<n 2)

flat-minus-two : FlatOutcome
flat-minus-two = fromℕ< (toℕ<n 254)

flat-four : FlatOutcome
flat-four = fromℕ< (toℕ<n 4)

flat-minus-four : FlatOutcome
flat-minus-four = fromℕ< (toℕ<n 252)

flat-eight : FlatOutcome
flat-eight = fromℕ< (toℕ<n 8)

flat-minus-eight : FlatOutcome
flat-minus-eight = fromℕ< (toℕ<n 248)

flat-sixteen : FlatOutcome
flat-sixteen = fromℕ< (toℕ<n 16)

flat-minus-sixteen : FlatOutcome
flat-minus-sixteen = fromℕ< (toℕ<n 240)

flatWeight-normalized : flatWeightSum 256 ≡ 256
flatWeight-normalized = refl

flatUnit-positive : flatWeight flat-one ≡ 1
flatUnit-positive = refl

flatUnit-negative-positive : flatWeight flat-minus-one ≡ 1
flatUnit-negative-positive = refl

flatZero-positive : flatWeight flat-zero ≡ 1
flatZero-positive = refl

flatPowerTwo-support :
  (flatWeight flat-two ≡ 1 × flatWeight flat-minus-two ≡ 1)
  × (flatWeight flat-four ≡ 1 × flatWeight flat-minus-four ≡ 1)
  × (flatWeight flat-eight ≡ 1 × flatWeight flat-minus-eight ≡ 1)
  × (flatWeight flat-sixteen ≡ 1 × flatWeight flat-minus-sixteen ≡ 1)
flatPowerTwo-support =
  (refl , refl) , (refl , refl) , (refl , refl) , (refl , refl)

-- Every one of the 256 outcomes has the same exact dyadic numerator.
flatCommonDenominator : ℕ
flatCommonDenominator = 256

flatDenominator-law : flatCommonDenominator ≡ 256
flatDenominator-law = refl
