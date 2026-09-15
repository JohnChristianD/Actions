{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.NegativeAlphaDyadicLog_test where

open import Agda.Builtin.Equality using (refl)
open import Data.Fin using (zero)
open import Exotic.ERL.FullCoupled.NegativeAlphaDyadicLog

test-log-zero : log2Dyadic zero ≡ log2Dyadic zero
test-log-zero = refl

test-bonus : ∀ k → negativeAlphaBonus k ≡ negativeAlphaBonus k
test-bonus k = refl

test-default-positive : positiveLogDefaultInit ≡ optimisticInit
test-default-positive = refl

test-default-negative : negativeLogDefaultInit ≡ pessimisticInit
test-default-negative = refl
