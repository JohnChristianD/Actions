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
open import Exotic.ERL.FullCoupled.CanonicalClosedLoopBenchV2

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
    (λ s a r → negativeMunchausenBinaryStep s a r 16)

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

banditCeterisParibusSuccess :
  success (episodeMetrics banditNoM) ≡ success (episodeMetrics banditNegativeM)
banditCeterisParibusSuccess = refl

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

mazeNegativeAgent : ClosedLoopAgent 4
mazeNegativeAgent =
  closedLoopAgent
    (λ s → lift4 (binaryAction s))
    (λ s a r → negativeMunchausenBinaryStep s (decode4 a) r 16)

mazeNoM : BenchSpec 4 P.MazeState
mazeNoM = benchSpec
  (closedLoopEnv P.mazeStep)
  agent4
  (P.mazeState 0 0 0 1 0)
  ablationInitialLearner
  1
  1
  (λ s with P.natEq (P.row s) (P.goalRow s)
   ... | P.yes with P.natEq (P.col s) (P.goalCol s)
   ...   | P.yes = 1
   ...   | P.no = 0
   ... | P.no = 0)

mazeNegativeM : BenchSpec 4 P.MazeState
mazeNegativeM = benchSpec
  (closedLoopEnv P.mazeStep)
  mazeNegativeAgent
  (P.mazeState 0 0 0 1 0)
  ablationInitialLearner
  1
  1
  (λ s with P.natEq (P.row s) (P.goalRow s)
   ... | P.yes with P.natEq (P.col s) (P.goalCol s)
   ...   | P.yes = 1
   ...   | P.no = 0
   ... | P.no = 0)

mazeCeterisParibusReturn :
  return (episodeMetrics mazeNoM) ≡ return (episodeMetrics mazeNegativeM)
mazeCeterisParibusReturn = refl
