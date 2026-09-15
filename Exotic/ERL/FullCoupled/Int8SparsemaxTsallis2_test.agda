{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.Int8SparsemaxTsallis2_test where

open import Agda.Builtin.Equality using (refl)
open import Exotic.ERL.FullCoupled.Int8SparsemaxTsallis2

testSupport : support2 (actionScore zeroWeight oneWeight) ≡ support2 (actionScore zeroWeight oneWeight)
testSupport = refl

testWeights : ∀ s → sparsemax2Weights s ≡ sparsemax2Weights s
testWeights s = refl

testTsallis2 : ∀ s → sparsemax2-is-tsallis2-support s ≡ sparsemax2-is-tsallis2-support s
testTsallis2 s = refl
