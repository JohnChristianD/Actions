{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GRUCoupled_test where

open import Exotic.ERL.FullCoupled.GRUCoupled using
  ( CoupledStep
  ; coupledReachability
  ; coupledPeriodOne
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; PeriodOne
  )
open import Exotic.ERL.Exploration.MethodLawCoupling using
  ( MR15Flat
  ; OpenESFlat
  ; NoisyNetGRUFlat
  )

mr15-safe : ∀ s t → Reach (CoupledStep MR15Flat) s t
mr15-safe = coupledReachability MR15Flat

openes-safe : ∀ s t → Reach (CoupledStep OpenESFlat) s t
openes-safe = coupledReachability OpenESFlat

noisynet-safe : ∀ s t → Reach (CoupledStep NoisyNetGRUFlat) s t
noisynet-safe = coupledReachability NoisyNetGRUFlat

mr15-period-one : PeriodOne (CoupledStep MR15Flat)
mr15-period-one = coupledPeriodOne MR15Flat

openes-period-one : PeriodOne (CoupledStep OpenESFlat)
openes-period-one = coupledPeriodOne OpenESFlat

noisynet-period-one : PeriodOne (CoupledStep NoisyNetGRUFlat)
noisynet-period-one = coupledPeriodOne NoisyNetGRUFlat
