{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalClosedLoopBenchV2 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat.DivMod using (m%n<n)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P
open import Exotic.ERL.FullCoupled.CanonicalClosedLoopInterface

initialLearnerV2 : FullLearnerState
initialLearnerV2 = fullLearnerState
  zero
  (watkinsState (criticState zero8 zero8) zero8 disabled)
  identityAttention
  (gruState zero8 identityGRUMatrices zeroGRUNoise zeroGlobalControl)
  (f4IntUState zero8 zero8 zero8 zero8 zero8)
  (normPair zero8 zero8)
  (lcbCountState zero zero zero)
  canonicalQLogControl
  (finiteRational 0 1 1)

lift4 : Fin 2 → Fin 4
lift4 a with toℕ a
... | zero = P.fin4 0
... | _ = P.fin4 3

decode4 : Fin 4 → Fin 2
decode4 a with toℕ a
... | zero = P.fin2 0
... | _ = P.fin2 1

lift5 : Fin 2 → Fin 5
lift5 a with toℕ a
... | zero = P.fin5 0
... | _ = P.fin5 4

decode5 : Fin 5 → Fin 2
decode5 a with toℕ a
... | zero = P.fin2 0
... | _ = P.fin2 1

lift6 : Fin 2 → Fin 6
lift6 a with toℕ a
... | zero = P.fin6 0
... | _ = P.fin6 4

decode6 : Fin 6 → Fin 2
decode6 a with toℕ a
... | zero = P.fin2 0
... | _ = P.fin2 1

lift3 : Fin 2 → Fin 3
lift3 a with toℕ a
... | zero = P.fin3 0
... | _ = P.fin3 2

decode3 : Fin 3 → Fin 2
decode3 a with toℕ a
... | zero = P.fin2 0
... | _ = P.fin2 1

agent4 : ClosedLoopAgent 4
agent4 = closedLoopAgent (λ s → lift4 (binaryAction s)) (λ s a r → binaryLearnerStep s (decode4 a) r)

agent5 : ClosedLoopAgent 5
agent5 = closedLoopAgent (λ s → lift5 (binaryAction s)) (λ s a r → binaryLearnerStep s (decode5 a) r)

agent6 : ClosedLoopAgent 6
agent6 = closedLoopAgent (λ s → lift6 (binaryAction s)) (λ s a r → binaryLearnerStep s (decode6 a) r)

agent3 : ClosedLoopAgent 3
agent3 = closedLoopAgent (λ s → lift3 (binaryAction s)) (λ s a r → binaryLearnerStep s (decode3 a) r)

knapsackSpec : BenchSpec 2 P.KnapsackState
knapsackSpec = benchSpec
  (closedLoopEnv P.knapsackStep)
  binaryAgent
  (P.knapsackState 0 3 0)
  initialLearnerV2
  2
  6
  (λ s with P.natEq (P.value s) 4
   ... | P.yes = 1
   ... | P.no = 0)

knapsackReturn : return (episodeMetrics knapsackSpec) ≡ 4
knapsackReturn = refl

knapsackRegret : regret (episodeMetrics knapsackSpec) ≡ 2
knapsackRegret = refl

knapsackSuccess : success (episodeMetrics knapsackSpec) ≡ 1
knapsackSuccess = refl

mazeSpec : BenchSpec 4 P.MazeState
mazeSpec = benchSpec
  (closedLoopEnv P.mazeStep)
  agent4
  (P.mazeState 0 0 0 0 0)
  initialLearnerV2
  1
  1
  (λ s with P.natEq (P.row s) (P.goalRow s)
   ... | P.yes with P.natEq (P.col s) (P.goalCol s)
   ...   | P.yes = 1
   ...   | P.no = 0
   ... | P.no = 0)

mazeReturn : return (episodeMetrics mazeSpec) ≡ 1
mazeReturn = refl

mazeRegret : regret (episodeMetrics mazeSpec) ≡ 0
mazeRegret = refl

mazeSuccess : success (episodeMetrics mazeSpec) ≡ 1
mazeSuccess = refl

metaMazeSpec : BenchSpec 4 P.MetaMazeState
metaMazeSpec = benchSpec
  (closedLoopEnv P.metaMazeStep)
  agent4
  (P.metaMazeState 0 0 0 0 0)
  initialLearnerV2
  1
  10
  (λ s with P.natEq (P.row s) (P.goalRow s)
   ... | P.yes with P.natEq (P.col s) (P.goalCol s)
   ...   | P.yes = 1
   ...   | P.no = 0
   ... | P.no = 0)

metaMazeReturn : return (episodeMetrics metaMazeSpec) ≡ 10
metaMazeReturn = refl

metaMazeSuccess : success (episodeMetrics metaMazeSpec) ≡ 1
metaMazeSuccess = refl

fourRoomsSpec : BenchSpec 4 P.MazeState
fourRoomsSpec = benchSpec
  (closedLoopEnv P.fourRoomsStep)
  agent4
  (P.mazeState 0 0 0 0 0)
  initialLearnerV2
  1
  1
  (λ s with P.natEq (P.row s) (P.goalRow s)
   ... | P.yes with P.natEq (P.col s) (P.goalCol s)
   ...   | P.yes = 1
   ...   | P.no = 0
   ... | P.no = 0)

fourRoomsReturn : return (episodeMetrics fourRoomsSpec) ≡ 1
fourRoomsReturn = refl

lbfSpec : BenchSpec 6 P.LBFState
lbfSpec = benchSpec
  (closedLoopEnv P.lbfStep)
  agent6
  (P.lbfState 0 0 0 0 0 0 1 0)
  initialLearnerV2
  1
  1
  (λ s with P.natEq (P.foodLevel s) 0
   ... | P.yes = 1
   ... | P.no = 0)

lbfReturn : return (episodeMetrics lbfSpec) ≡ 1
lbfReturn = refl

lbfSuccess : success (episodeMetrics lbfSpec) ≡ 1
lbfSuccess = refl

pongSpec : BenchSpec 3 P.PongState
pongSpec = benchSpec
  (closedLoopEnv P.pongStep)
  agent3
  (P.pongState 0 0 0 0 1 1 0)
  initialLearnerV2
  2
  2
  (λ s → 1)

pongReturn : return (episodeMetrics pongSpec) ≡ 2
pongReturn = refl

memoryChainSpec : BenchSpec 2 P.MemoryChainState
memoryChainSpec = benchSpec
  (closedLoopEnv P.memoryChainStep)
  binaryAgent
  (P.memoryChainState 1 1 0)
  initialLearnerV2
  7
  1
  (λ s with P.natEq (P.time s) 7
   ... | P.yes = 1
   ... | P.no = 0)

memoryChainReturn : return (episodeMetrics memoryChainSpec) ≡ 1
memoryChainReturn = refl

discountingChainSpec : BenchSpec 5 P.DiscountingChainState
discountingChainSpec = benchSpec
  (closedLoopEnv P.discountingChainStep)
  agent5
  (P.discountingChainState 0 0)
  initialLearnerV2
  1
  5
  (λ s → 1)

discountingChainReturn : return (episodeMetrics discountingChainSpec) ≡ 5
discountingChainReturn = refl

rockSampleSpec : BenchSpec 6 P.RockSampleState
rockSampleSpec = benchSpec
  (closedLoopEnv P.rockSampleStep)
  agent6
  (P.rockSampleState 3 0 1 0)
  initialLearnerV2
  1
  1
  (λ s with P.natEq (P.rockGood s) 0
   ... | P.yes = 1
   ... | P.no = 0)

rockSampleReturn : return (episodeMetrics rockSampleSpec) ≡ 1
rockSampleReturn = refl

rockSampleSuccess : success (episodeMetrics rockSampleSpec) ≡ 1
rockSampleSuccess = refl
