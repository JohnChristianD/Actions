{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalMunchausenAblation_test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (Fin; fromℕ<)
open import Data.Nat.DivMod using (m%n<n)

open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P
open import Exotic.ERL.FullCoupled.CanonicalClosedLoopInterface
open import Exotic.ERL.FullCoupled.CanonicalMunchausenAblation

ablationInitialLearner : FullLearnerState
ablationInitialLearner = fullLearnerState
  zero
  (watkinsState (criticState zero8 zero8) zero8 disabled)
  identityAttention
  (gruState zero8 identityGRUMatrices zeroGRUNoise zeroGlobalControl)
  (f4IntUState zero8 zero8 zero8 zero8 zero8)
  (normPair zero8 zero8)
  (lcbCountState zero zero zero)
  canonicalQLogControl
  (finiteRational 0 1 1)

negativeAgent : ClosedLoopAgent 2
negativeAgent =
  closedLoopAgent
    binaryAction
    (λ s a r → negativeMunchausenBinaryStep s a r 0)

banditNoM : BenchSpec 2 P.BernoulliBanditState
banditNoM = benchSpec
  (closedLoopEnv P.bernoulliBanditStep)
  binaryAgent
  (P.bernoulliBanditState 1 0 0 0)
  ablationInitialLearner
  4
  4
  (λ s with P.natEq (P.lastReward s) 1
   ... | P.yes = 1
   ... | P.no = 0)

banditNegativeM : BenchSpec 2 P.BernoulliBanditState
banditNegativeM = benchSpec
  (closedLoopEnv P.bernoulliBanditStep)
  negativeAgent
  (P.bernoulliBanditState 1 0 0 0)
  ablationInitialLearner
  4
  4
  (λ s with P.natEq (P.lastReward s) 1
   ... | P.yes = 1
   ... | P.no = 0)

banditNoMReturn : return (episodeMetrics banditNoM) ≡ 4
banditNoMReturn = refl

banditNegativeMReturn : return (episodeMetrics banditNegativeM) ≡ 4
banditNegativeMReturn = refl

banditCeterisParibusReturn :
  return (episodeMetrics banditNoM) ≡ return (episodeMetrics banditNegativeM)
banditCeterisParibusReturn = refl

cartPoleNoM : BenchSpec 2 P.CartPoleQuantizedState
cartPoleNoM = benchSpec
  (closedLoopEnv P.cartPoleQuantizedStep)
  binaryAgent
  (P.cartPoleQuantizedState 0 0 0 0 0)
  ablationInitialLearner
  4
  0
  (λ s → 0)

cartPoleNegativeM : BenchSpec 2 P.CartPoleQuantizedState
cartPoleNegativeM = benchSpec
  (closedLoopEnv P.cartPoleQuantizedStep)
  negativeAgent
  (P.cartPoleQuantizedState 0 0 0 0 0)
  ablationInitialLearner
  4
  0
  (λ s → 0)

cartPoleCeterisParibusReturn :
  return (episodeMetrics cartPoleNoM) ≡ return (episodeMetrics cartPoleNegativeM)
cartPoleCeterisParibusReturn = refl
