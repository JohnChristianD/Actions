{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GRUCoupled_test where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.FullCoupled.GRUCoupled using
  ( GlobalCoupledState
  ; CoupledStep
  ; coupledReachability
  ; coupledSelfLoop
  ; coupledPeriodOne
  ; preprocessed
  )
open import Exotic.ERL.Exploration.MethodLawCoupling using
  ( MR15Flat
  ; OpenESFlat
  ; NoisyNetGRUFlat
  )

mr15-safe : ∀ s t → _
mr15-safe = coupledReachability MR15Flat

openes-safe : ∀ s t → _
openes-safe = coupledReachability OpenESFlat

noisynet-safe : ∀ s t → _
noisynet-safe = coupledReachability NoisyNetGRUFlat

mr15-period-one : _
mr15-period-one = coupledPeriodOne MR15Flat

openes-period-one : _
openes-period-one = coupledPeriodOne OpenESFlat

noisynet-period-one : _
noisynet-period-one = coupledPeriodOne NoisyNetGRUFlat
