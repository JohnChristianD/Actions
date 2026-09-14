{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.AllSafeCombined where

open import Exotic.ERL.FullCoupled.GRUCoupled using
  ( GlobalCoupledState
  ; preprocessed
  ; coupledReachability
  ; coupledSelfLoop
  ; coupledPeriodOne
  )
open import Exotic.ERL.Exploration.MethodLawCoupling using
  ( MR15Flat
  ; OpenESFlat
  ; NoisyNetGRUFlat
  )

canonicalMR15Reachability = coupledReachability MR15Flat
canonicalMR15SelfLoop = coupledSelfLoop MR15Flat
canonicalMR15PeriodOne = coupledPeriodOne MR15Flat

canonicalOpenESReachability = coupledReachability OpenESFlat
canonicalOpenESSelfLoop = coupledSelfLoop OpenESFlat
canonicalOpenESPeriodOne = coupledPeriodOne OpenESFlat

canonicalNoisyNetReachability = coupledReachability NoisyNetGRUFlat
canonicalNoisyNetSelfLoop = coupledSelfLoop NoisyNetGRUFlat
canonicalNoisyNetPeriodOne = coupledPeriodOne NoisyNetGRUFlat
