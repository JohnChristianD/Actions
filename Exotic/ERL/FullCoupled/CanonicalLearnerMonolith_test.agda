{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalLearnerMonolith_test where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith

scores2 : V (Fin 256) 2
scores2 = 200 ∷ 100 ∷ []

scores3 : V (Fin 256) 3
scores3 = 128 ∷ 128 ∷ 128 ∷ []

test-sparsemax-2-action : sparsemaxA scores2 ≡ frac 1 1 ∷ frac 0 1 ∷ []
test-sparsemax-2-action = refl

test-sparsemax-3-action : sparsemaxA scores3 ≡ frac 1 3 ∷ frac 1 3 ∷ frac 1 3 ∷ []
test-sparsemax-3-action = refl

test-sparsemax-policy-2 : sparsemaxPolicyA scores2 ≡ zero
test-sparsemax-policy-2 = refl

test-sparsemax-policy-3 : sparsemaxPolicyA scores3 ≡ zero
test-sparsemax-policy-3 = refl
