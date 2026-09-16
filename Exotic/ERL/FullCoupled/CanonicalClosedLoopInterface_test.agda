{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalClosedLoopInterface_test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat.DivMod using (m%n<n)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P
open import Exotic.ERL.FullCoupled.CanonicalClosedLoopInterface

initialLearner : FullLearnerState
initialLearner = fullLearnerState
  zero
  (watkinsState (criticState zero8 zero8) zero8 disabled)
  identityAttention
  (gruState zero8 identityGRUMatrices zeroGRUNoise zeroGlobalControl)
  (f4IntUState zero8 zero8 zero8 zero8 zero8)
  (normPair zero8 zero8)
  (lcbCountState zero zero zero)
  canonicalQLogControl
  (finiteRational 0 1 1)

banditEnv : ClosedLoopEnv 2 P.BernoulliBanditState
banditEnv = closedLoopEnv P.bernoulliBanditStep

banditSpec : BenchSpec 2 P.BernoulliBanditState
banditSpec = benchSpec
  banditEnv
  binaryAgent
  (P.bernoulliBanditState 1 0 0 0)
  initialLearner
  4
  4
  (λ s with P.natEq (P.lastReward s) 1
   ... | P.yes = 1
   ... | P.no = 0)

banditReturn : return (episodeMetrics banditSpec) ≡ 4
banditReturn = refl

banditRegret : regret (episodeMetrics banditSpec) ≡ 0
banditRegret = refl

banditSuccess : success (episodeMetrics banditSpec) ≡ 1
banditSuccess = refl

banditSteps : stepsTaken (episodeMetrics banditSpec) ≡ 4
banditSteps = refl

cartPoleEnv : ClosedLoopEnv 2 P.CartPoleQuantizedState
cartPoleEnv = closedLoopEnv P.cartPoleQuantizedStep

cartPoleSpec : BenchSpec 2 P.CartPoleQuantizedState
cartPoleSpec = benchSpec
  cartPoleEnv
  binaryAgent
  (P.cartPoleQuantizedState 0 0 0 0 0)
  initialLearner
  4
  0
  (λ s → 0)

cartPoleReturn : return (episodeMetrics cartPoleSpec) ≡ 0
cartPoleReturn = refl

cartPoleSteps : stepsTaken (episodeMetrics cartPoleSpec) ≡ 4
cartPoleSteps = refl

cartPoleClock : clock (finalLearner (runEpisode cartPoleSpec)) ≡ 4
cartPoleClock = refl
