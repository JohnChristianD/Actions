{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ActualCoupledLearner_test where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (one8)
open import Exotic.ERL.FullCoupled.ActualCoupledLearner using (learningWitness; State.a)
open import Exotic.ERL.FullCoupled.F4IntKernel using (theta)

checkLearning : theta (State.a learningWitness) ≡ one8
checkLearning = refl
