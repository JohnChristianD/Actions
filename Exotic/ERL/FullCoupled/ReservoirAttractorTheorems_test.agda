{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ReservoirAttractorTheorems_test where

open import Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith as T
open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L

finite-core-cycle : ∀ (R : L.Int8 → L.Int8) (s : L.Int8) →
  T.FiniteOrbitEventuallyPeriodic R s
finite-core-cycle = T.int8-orbit-eventually-periodic
