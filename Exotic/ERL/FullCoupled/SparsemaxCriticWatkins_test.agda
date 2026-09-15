{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SparsemaxCriticWatkins_test where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (zero8; one8)
open import Exotic.ERL.FullCoupled.Int8SparsemaxTsallis2 using
  ( actionScore
  ; sparsemax2Weights
  )
open import Exotic.ERL.FullCoupled.SparsemaxCriticWatkins

critic0 : CriticState
critic0 = criticState zero8 one8

test-policy : criticSparsemaxPolicy critic0 ≡ sparsemax2Weights (actionScore zero8 one8)
test-policy = refl
