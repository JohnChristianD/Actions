{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalEndToEndFaithfulBench2 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using ()
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalClosedLoopLearner
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P
open import Exotic.ERL.FullCoupled.CanonicalFaithfulFixedGamePorts
open import Exotic.ERL.FullCoupled.CanonicalFaithfulGameVariants

portReward : P.Int8 → Int8
portReward r = int8OfNat (P.toℕ (P.code r))

benchWatkinsKernel : WatkinsKernel
benchWatkinsKernel = mkWatkinsKernel (λ q r → q) (λ q r → disabled) (λ t g → t)

benchAttentionStep : LearnedSparsemaxAttention → Int8 → LearnedSparsemaxAttention
benchAttentionStep a r = a

benchAttentionToGRU : WalshVec4 → Int8
benchAttentionToGRU w = zero8

benchOptimizerKernel : F4IntUKernel
benchOptimizerKernel = f4IntUKernel zero8

benchLCBKernel : LCBCountKernel
benchLCBKernel = lcbCountKernel finiteLCBBonus8

benchKernel : FullLearnerKernel
benchKernel = mkFullLearnerKernel benchWatkinsKernel benchAttentionStep
  benchAttentionToGRU benchOptimizerKernel benchLCBKernel

benchLearnerInitial : FullLearnerState
benchLearnerInitial = fullLearnerState zero
  (watkinsState (criticState zero8 zero8) zero8 disabled)
  identityAttention
  (gruState zero8 identityGRUMatrices zeroGRUNoise zeroGlobalControl)
  (f4IntUState zero8 zero8 zero8 zero8 zero8)
  (normPair zero8 zero8)
  (lcbCountState zero zero zero)
  canonicalQLogControl (finiteRational 0 1 1)

canonicalBinaryAction : FullLearnerState → Fin 2
canonicalBinaryAction s with policyChoosesLeft (canonicalPolicy benchKernel s)
... | enabled = fromℕ< (m%n<n 0 2)
... | disabled = fromℕ< (m%n<n 1 2)

cycle2 : Nat → Nat
cycle2 zero = zero
cycle2 (suc zero) = suc zero
cycle2 (suc (suc n)) = cycle2 n

cycle3 : Nat → Nat
cycle3 zero = zero
cycle3 (suc zero) = suc zero
cycle3 (suc (suc zero)) = suc (suc zero)
cycle3 (suc (suc (suc n))) = cycle3 n

cycle4 : Nat → Nat
cycle4 zero = zero
cycle4 (suc zero) = suc zero
cycle4 (suc (suc zero)) = suc (suc zero)
cycle4 (suc (suc (suc zero))) = suc (suc (suc zero))
cycle4 (suc (suc (suc (suc n)))) = cycle4 n

lift2 : FullLearnerState → Fin 2
lift2 = canonicalBinaryAction

lift3 : FullLearnerState → Fin 3
lift3 s = fromℕ< (m%n<n (cycle3 (clock s) + toℕ (canonicalBinaryAction s)) 3)

lift4 : FullLearnerState → Fin 4
lift4 s = fromℕ< (m%n<n ((cycle2 (clock s) * 2) + toℕ (canonicalBinaryAction s)) 4)

lift5 : FullLearnerState → Fin 5
lift5 s = fromℕ< (m%n<n ((cycle4 (clock s) * 2) + toℕ (canonicalBinaryAction s)) 5)

lift6 : FullLearnerState → Fin 6
lift6 s = fromℕ< (m%n<n ((cycle3 (clock s) * 2) + toℕ (canonicalBinaryAction s)) 6)

fourRoomsStepExact : Fin 4 → P.MazeState → P.StepResult P.MazeState
fourRoomsStepExact a s with P.mazeMove a (P.row s , P.col s)
... | nr , nc with fourRoomsOpenExact nr nc
...   | P.no = P.stepResult (P.int8OfNat (P.row s + P.col s))
      (P.mazeState (P.row s) (P.col s) (P.goalRow s) (P.goalCol s) (suc (P.time s))) P.zero8 P.no
...   | P.yes with P.natEq nr (P.goalRow s)
...     | P.yes with P.natEq nc (P.goalCol s)
...       | P.yes = P.stepResult (P.int8OfNat (nr + nc))
          (P.mazeState nr nc (P.goalRow s) (P.goalCol s) (suc (P.time s))) P.one8 P.yes
...       | P.no = P.stepResult (P.int8OfNat (nr + nc))
          (P.mazeState nr nc (P.goalRow s) (P.goalCol s) (suc (P.time s))) P.zero8 P.no
...     | P.no = P.stepResult (P.int8OfNat (nr + nc))
        (P.mazeState nr nc (P.goalRow s) (P.goalCol s) (suc (P.time s))) P.zero8 P.no

record BenchSpec (N : Nat) (S : Set) : Set₁ where
  constructor benchSpec
  field initial : S
        horizon referenceReturn : Nat
        choose : FullLearnerState → Fin N
        learnerAction : FullLearnerState → Fin 2
        step : Fin N → S → P.StepResult S
        success : Nat → S → Nat
open BenchSpec public

record BenchRun (S : Set) : Set where
  constructor benchRun
  field environment : S
        learner : FullLearnerState
        totalReturn steps : Nat
open BenchRun public

runBench : ∀ {N S} → BenchSpec N S → FullLearnerState → BenchRun S
runBench spec learner = loop (horizon spec) learner (initial spec) zero zero
  where
    loop : Nat → FullLearnerState → S → Nat → Nat → BenchRun S
    loop zero l e total steps = benchRun e l total steps
    loop (suc n) l e total steps with step spec (choose spec l) e
    ... | P.stepResult obs e' r done with done
    ...   | P.yes = benchRun e'
          (closedLoopLearnerStep benchKernel l (learnerAction spec l) (portReward r))
          (total + toℕ (P.code r)) (suc steps)
    ...   | P.no = loop n
          (closedLoopLearnerStep benchKernel l (learnerAction spec l) (portReward r))
          e' (total + toℕ (P.code r)) (suc steps)

record BenchMetrics (S : Set) : Set where
  constructor benchMetrics
  field metricReturn metricReference metricRegret metricSuccess metricSteps : Nat
open BenchMetrics public

metricsOf : ∀ {N S} → BenchSpec N S → FullLearnerState → BenchMetrics S
metricsOf spec l = let r = runBench spec l in benchMetrics
  (totalReturn r) (referenceReturn spec)
  (referenceReturn spec ∸ totalReturn r)
  (success spec (totalReturn r) (environment r))
  (steps r)

cartPoleSpec : BenchSpec 2 P.CartPoleQuantizedState
cartPoleSpec = benchSpec (P.cartPoleQuantizedState 1 0 0 0 0) 16 500
  lift2 lift2 P.cartPoleQuantizedStep
  (λ total s with P.natEq (P.time s) 16
  ... | P.yes = 1
  ... | P.no = 0)

banditBest0Spec : BenchSpec 2 P.BernoulliBanditState
banditBest0Spec = benchSpec (P.bernoulliBanditState 0 0 0 0) 16 16
  lift2 lift2 P.bernoulliBanditStep
  (λ total s with P.natEq total 16
  ... | P.yes = 1
  ... | P.no = 0)

banditBest1Spec : BenchSpec 2 P.BernoulliBanditState
banditBest1Spec = benchSpec (P.bernoulliBanditState 1 0 0 0) 16 16
  lift2 lift2 P.bernoulliBanditStep
  (λ total s with P.natEq total 16
  ... | P.yes = 1
  ... | P.no = 0)

knapsackSpec : BenchSpec 2 FaithfulKnapsackState
knapsackSpec = benchSpec faithfulFixedKnapsackInitial 8 6 lift2 lift2
  (λ a s with toℕ a
  ... | zero = faithfulKnapsackStep item0 s
  ... | _ = faithfulKnapsackStep item1 s)
  (λ total s with natEq (value s) 6
  ... | yes = 1
  ... | no = 0)

mazeV0Spec : BenchSpec 4 P.MazeState
mazeV0Spec = benchSpec faithfulFixedMazeInitial 16 1 lift4 lift2 faithfulToyMazeStep
  (λ total s with P.natEq (P.row s) (P.goalRow s)
  ... | P.yes with P.natEq (P.col s) (P.goalCol s)
  ...   | P.yes = 1
  ...   | P.no = 0
  ... | P.no = 0)

metaMazeSpec : BenchSpec 4 P.MetaMazeState
metaMazeSpec = benchSpec (P.metaMazeState 0 0 4 4 0) 16 10 lift4 lift2 P.metaMazeStep
  (λ total s with P.natEq (P.row s) (P.goalRow s)
  ... | P.yes with P.natEq (P.col s) (P.goalCol s)
  ...   | P.yes = 1
  ...   | P.no = 0
  ... | P.no = 0)

fourRoomsSpec : BenchSpec 4 P.MazeState
fourRoomsSpec = benchSpec (P.mazeState 1 1 9 11 0) 16 1 lift4 lift2 fourRoomsStepExact
  (λ total s with P.natEq (P.row s) (P.goalRow s)
  ... | P.yes with P.natEq (P.col s) (P.goalCol s)
  ...   | P.yes = 1
  ...   | P.no = 0
  ... | P.no = 0)

levelBasedForagingSpec : BenchSpec 6 P.LBFState
levelBasedForagingSpec = benchSpec (P.lbfState 0 0 1 1 0 1 1 0) 16 1
  lift6 lift2 P.lbfStep
  (λ total s with P.natEq (P.foodLevel s) 0
  ... | P.yes = 1
  ... | P.no = 0)

pongSpec : BenchSpec 3 P.PongState
pongSpec = benchSpec (P.pongState 0 0 0 0 1 1 0) 16 16 lift3 lift2 P.pongStep
  (λ total s with P.natEq total 16
  ... | P.yes = 1
  ... | P.no = 0)

memoryChainSpec : BenchSpec 2 FaithfulMemoryChainState
memoryChainSpec = benchSpec faithfulFixedMemoryInitial 6 1 lift2 lift2 faithfulMemoryChainStep
  (λ total s with P.natEq total 1
  ... | P.yes = 1
  ... | P.no = 0)

discountingChainSpec : BenchSpec 5 FaithfulDiscountingChainState
discountingChainSpec = benchSpec faithfulFixedDiscountingInitial 4 11 lift5 lift2 faithfulDiscountingChainStep
  (λ total s with P.natEq total 10
  ... | P.yes = 1
  ... | P.no = 0)

rockSampleSpec : BenchSpec 6 P.RockSampleState
rockSampleSpec = benchSpec (P.rockSampleState 0 0 1 0) 16 1 lift6 lift2 P.rockSampleStep
  (λ total s with P.natEq (P.rockGood s) 0
  ... | P.yes = 1
  ... | P.no = 0)

cartPoleMetrics = metricsOf cartPoleSpec benchLearnerInitial
banditBest0Metrics = metricsOf banditBest0Spec benchLearnerInitial
banditBest1Metrics = metricsOf banditBest1Spec benchLearnerInitial
knapsackMetrics = metricsOf knapsackSpec benchLearnerInitial
mazeV0Metrics = metricsOf mazeV0Spec benchLearnerInitial
metaMazeMetrics = metricsOf metaMazeSpec benchLearnerInitial
fourRoomsMetrics = metricsOf fourRoomsSpec benchLearnerInitial
levelBasedForagingMetrics = metricsOf levelBasedForagingSpec benchLearnerInitial
pongMetrics = metricsOf pongSpec benchLearnerInitial
memoryChainMetrics = metricsOf memoryChainSpec benchLearnerInitial
discountingChainMetrics = metricsOf discountingChainSpec benchLearnerInitial
rockSampleMetrics = metricsOf rockSampleSpec benchLearnerInitial

check-cartpole : metricReturn cartPoleMetrics ≡ 0
check-cartpole = refl
check-bandit0 : metricReturn banditBest0Metrics ≡ 14
check-bandit0 = refl
check-bandit1 : metricReturn banditBest1Metrics ≡ 14
check-bandit1 = refl
check-knapsack : metricReturn knapsackMetrics ≡ 4
check-knapsack = refl
check-maze : metricReturn mazeV0Metrics ≡ 0
check-maze = refl
check-metaMaze : metricReturn metaMazeMetrics ≡ 0
check-metaMaze = refl
check-fourRooms : metricReturn fourRoomsMetrics ≡ 0
check-fourRooms = refl
check-lbf : metricReturn levelBasedForagingMetrics ≡ 0
check-lbf = refl
check-pong : metricReturn pongMetrics ≡ 16
check-pong = refl
check-memory : metricReturn memoryChainMetrics ≡ 1
check-memory = refl
check-discounting : metricReturn discountingChainMetrics ≡ 10
check-discounting = refl
check-rockSample : metricReturn rockSampleMetrics ≡ 0
check-rockSample = refl

closedLoopBench-action-source : ∀ s → canonicalBinaryAction s ≡ lift2 s
closedLoopBench-action-source s = refl