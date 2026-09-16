{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalEndToEndFaithfulBench where

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

benchWatkinsKernel : WatkinsKernel
benchWatkinsKernel = mkWatkinsKernel
  (λ q r → q)
  (λ q r → disabled)
  (λ t g → t)

benchAttentionStep : LearnedSparsemaxAttention → Int8 → LearnedSparsemaxAttention
benchAttentionStep a r = a

benchAttentionToGRU : WalshVec4 → Int8
benchAttentionToGRU w = zero8

benchOptimizerKernel : F4IntUKernel
benchOptimizerKernel = f4IntUKernel zero8

benchLCBKernel : LCBCountKernel
benchLCBKernel = lcbCountKernel finiteLCBBonus8

benchKernel : FullLearnerKernel
benchKernel = mkFullLearnerKernel
  benchWatkinsKernel
  benchAttentionStep
  benchAttentionToGRU
  benchOptimizerKernel
  benchLCBKernel

benchLearnerInitial : FullLearnerState
benchLearnerInitial = fullLearnerState
  zero
  (watkinsState (criticState zero8 zero8) zero8 disabled)
  identityAttention
  (gruState zero8 identityGRUMatrices zeroGRUNoise zeroGlobalControl)
  (f4IntUState zero8 zero8 zero8 zero8 zero8)
  (normPair zero8 zero8)
  (lcbCountState zero zero zero)
  canonicalQLogControl
  (finiteRational 0 1 1)

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
  field
    initial : S
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
          (closedLoopLearnerStep benchKernel l (learnerAction spec l) (P.portReward r))
          (total + toℕ (P.code r)) (suc steps)
    ...   | P.no = loop n
          (closedLoopLearnerStep benchKernel l (learnerAction spec l) (P.portReward r))
          e' (total + toℕ (P.code r)) (suc steps)

record BenchMetrics (S : Set) : Set where
  constructor benchMetrics
  field metricReturn metricReference metricRegret metricSuccess metricSteps : Nat
open BenchMetrics public

metricsOf : ∀ {N S} → BenchSpec N S → FullLearnerState → BenchMetrics S
metricsOf spec l =
  let r = runBench spec l
  in benchMetrics
    (totalReturn r)
    (referenceReturn spec)
    (referenceReturn spec ∸ totalReturn r)
    (success spec (totalReturn r) (environment r))
    (steps r)

cartPoleSpec : BenchSpec 2 P.CartPoleQuantizedState
cartPoleSpec = benchSpec
  (P.cartPoleQuantizedState 1 0 0 0 0)
  16 500
  lift2
  lift2
  P.cartPoleQuantizedStep
  (λ total s with P.natEq (P.time s) 16
  ... | P.yes = 1
  ... | P.no = 0)

banditBest0Spec : BenchSpec 2 P.BernoulliBanditState
banditBest0Spec = benchSpec
  (P.bernoulliBanditState 0 0 0 0)
  16 16
  lift2
  lift2
  P.bernoulliBanditStep
  (λ total s with P.natEq total 16
  ... | P.yes = 1
  ... | P.no = 0)

banditBest1Spec : BenchSpec 2 P.BernoulliBanditState
banditBest1Spec = benchSpec
  (P.bernoulliBanditState 1 0 0 0)
  16 16
  lift2
  lift2
  P.bernoulliBanditStep
  (λ total s with P.natEq total 16
  ... | P.yes = 1
  ... | P.no = 0)

knapsackSpec : BenchSpec 2 FaithfulKnapsackState
knapsackSpec = benchSpec
  faithfulFixedKnapsackInitial
  8 6
  lift2
  lift2
  (λ a s with toℕ a
  ... | zero = faithfulKnapsackStep item0 s
  ... | _ = faithfulKnapsackStep item1 s)
  (λ total s with natEq (value s) 6
  ... | yes = 1
  ... | no = 0)

mazeV0Spec : BenchSpec 4 P.MazeState
mazeV0Spec = benchSpec
  faithfulFixedMazeInitial
  16 1
  lift4
  lift2
  faithfulToyMazeStep
  (λ total s with P.natEq (P.row s) (P.goalRow s)
  ... | P.yes with P.natEq (P.col s) (P.goalCol s)
  ...   | P.yes = 1
  ...   | P.no = 0
  ... | P.no = 0)

metaMazeSpec : BenchSpec 4 P.MetaMazeState
metaMazeSpec = benchSpec
  (P.metaMazeState 0 0 4 4 0)
  16 10
  lift4
  lift2
  P.metaMazeStep
  (λ total s with P.natEq (P.row s) (P.goalRow s)
  ... | P.yes with P.natEq (P.col s) (P.goalCol s)
  ...   | P.yes = 1
  ...   | P.no = 0
  ... | P.no = 0)

fourRoomsSpec : BenchSpec 4 P.MazeState
fourRoomsSpec = benchSpec
  (P.mazeState 1 1 9 11 0)
  16 1
  lift4
  lift2
  fourRoomsStepExact
  (λ total s with P.natEq (P.row s) (P.goalRow s)
  ... | P.yes with P.natEq (P.col s) (P.goalCol s)
  ...   | P.yes = 1
  ...   | P.no = 0
  ... | P.no = 0)

levelBasedForagingSpec : BenchSpec 6 P.LBFState
levelBasedForagingSpec = benchSpec
  (P.lbfState 0 0 1 1 0 1 1 0)
  16 1
  lift6
  lift2
  P.lbfStep
  (λ total s with P.natEq (P.foodLevel s) 0
  ... | P.yes = 1
  ... | P.no = 0)

pongSpec : BenchSpec 3 P.PongState
pongSpec = benchSpec
  (P.pongState 0 0 0 0 1 1 0)
  16 16
  lift3
  lift2
  P.pongStep
  (λ total s with P.natEq total 16
  ... | P.yes = 1
  ... | P.no = 0)

memoryChainSpec : BenchSpec 2 FaithfulMemoryChainState
memoryChainSpec = benchSpec
  faithfulFixedMemoryInitial
  6 1
  lift2
  lift2
  faithfulMemoryChainStep
  (λ total s with P.natEq total 1
  ... | P.yes = 1
  ... | P.no = 0)

discountingChainSpec : BenchSpec 5 FaithfulDiscountingChainState
discountingChainSpec = benchSpec
  faithfulFixedDiscountingInitial
  4 11
  lift5
  lift2
  faithfulDiscountingChainStep
  (λ total s with P.natEq total 10
  ... | P.yes = 1
  ... | P.no = 0)

rockSampleSpec : BenchSpec 6 P.RockSampleState
rockSampleSpec = benchSpec
  (P.rockSampleState 0 0 1 0)
  16 1
  lift6
  lift2
  P.rockSampleStep
  (λ total s with P.natEq (P.rockGood s) 0
  ... | P.yes = 1
  ... | P.no = 0)

cartPoleMetrics : BenchMetrics P.CartPoleQuantizedState
cartPoleMetrics = metricsOf cartPoleSpec benchLearnerInitial

banditBest0Metrics : BenchMetrics P.BernoulliBanditState
banditBest0Metrics = metricsOf banditBest0Spec benchLearnerInitial

banditBest1Metrics : BenchMetrics P.BernoulliBanditState
banditBest1Metrics = metricsOf banditBest1Spec benchLearnerInitial

knapsackMetrics : BenchMetrics FaithfulKnapsackState
knapsackMetrics = metricsOf knapsackSpec benchLearnerInitial

mazeV0Metrics : BenchMetrics P.MazeState
mazeV0Metrics = metricsOf mazeV0Spec benchLearnerInitial

metaMazeMetrics : BenchMetrics P.MetaMazeState
metaMazeMetrics = metricsOf metaMazeSpec benchLearnerInitial

fourRoomsMetrics : BenchMetrics P.MazeState
fourRoomsMetrics = metricsOf fourRoomsSpec benchLearnerInitial

levelBasedForagingMetrics : BenchMetrics P.LBFState
levelBasedForagingMetrics = metricsOf levelBasedForagingSpec benchLearnerInitial

pongMetrics : BenchMetrics P.PongState
pongMetrics = metricsOf pongSpec benchLearnerInitial

memoryChainMetrics : BenchMetrics FaithfulMemoryChainState
memoryChainMetrics = metricsOf memoryChainSpec benchLearnerInitial

discountingChainMetrics : BenchMetrics FaithfulDiscountingChainState
discountingChainMetrics = metricsOf discountingChainSpec benchLearnerInitial

rockSampleMetrics : BenchMetrics P.RockSampleState
rockSampleMetrics = metricsOf rockSampleSpec benchLearnerInitial

benchResults-record :
  BenchMetrics P.CartPoleQuantizedState ×
  BenchMetrics P.BernoulliBanditState ×
  BenchMetrics FaithfulKnapsackState ×
  BenchMetrics P.MazeState ×
  BenchMetrics P.MetaMazeState ×
  BenchMetrics P.PongState
benchResults-record = cartPoleMetrics ,
  (banditBest1Metrics ,
   (knapsackMetrics ,
    (mazeV0Metrics ,
     (metaMazeMetrics , pongMetrics))))

check-cartpole-return : metricReturn cartPoleMetrics ≡ 0
check-cartpole-return = refl
check-cartpole-regret : metricRegret cartPoleMetrics ≡ 500
check-cartpole-regret = refl
check-cartpole-success : metricSuccess cartPoleMetrics ≡ 1
check-cartpole-success = refl

check-bandit-best0-return : metricReturn banditBest0Metrics ≡ 14
check-bandit-best0-return = refl
check-bandit-best0-regret : metricRegret banditBest0Metrics ≡ 2
check-bandit-best0-regret = refl
check-bandit-best0-success : metricSuccess banditBest0Metrics ≡ 0
check-bandit-best0-success = refl

check-bandit-best1-return : metricReturn banditBest1Metrics ≡ 14
check-bandit-best1-return = refl
check-bandit-best1-regret : metricRegret banditBest1Metrics ≡ 2
check-bandit-best1-regret = refl
check-bandit-best1-success : metricSuccess banditBest1Metrics ≡ 0
check-bandit-best1-success = refl

check-knapsack-return : metricReturn knapsackMetrics ≡ 4
check-knapsack-return = refl
check-knapsack-regret : metricRegret knapsackMetrics ≡ 2
check-knapsack-regret = refl
check-knapsack-success : metricSuccess knapsackMetrics ≡ 0
check-knapsack-success = refl

check-maze-return : metricReturn mazeV0Metrics ≡ 0
check-maze-return = refl
check-maze-regret : metricRegret mazeV0Metrics ≡ 1
check-maze-regret = refl
check-maze-success : metricSuccess mazeV0Metrics ≡ 0
check-maze-success = refl

check-metaMaze-return : metricReturn metaMazeMetrics ≡ 0
check-metaMaze-return = refl
check-metaMaze-regret : metricRegret metaMazeMetrics ≡ 10
check-metaMaze-regret = refl
check-metaMaze-success : metricSuccess metaMazeMetrics ≡ 0
check-metaMaze-success = refl

check-fourRooms-return : metricReturn fourRoomsMetrics ≡ 0
check-fourRooms-return = refl
check-fourRooms-regret : metricRegret fourRoomsMetrics ≡ 1
check-fourRooms-regret = refl
check-fourRooms-success : metricSuccess fourRoomsMetrics ≡ 0
check-fourRooms-success = refl

check-levelBasedForaging-return : metricReturn levelBasedForagingMetrics ≡ 0
check-levelBasedForaging-return = refl
check-levelBasedForaging-regret : metricRegret levelBasedForagingMetrics ≡ 1
check-levelBasedForaging-regret = refl
check-levelBasedForaging-success : metricSuccess levelBasedForagingMetrics ≡ 0
check-levelBasedForaging-success = refl

check-pong-return : metricReturn pongMetrics ≡ 16
check-pong-return = refl
check-pong-regret : metricRegret pongMetrics ≡ 0
check-pong-regret = refl
check-pong-success : metricSuccess pongMetrics ≡ 1
check-pong-success = refl

check-memoryChain-return : metricReturn memoryChainMetrics ≡ 1
check-memoryChain-return = refl
check-memoryChain-regret : metricRegret memoryChainMetrics ≡ 0
check-memoryChain-regret = refl
check-memoryChain-success : metricSuccess memoryChainMetrics ≡ 1
check-memoryChain-success = refl

check-discountingChain-return-x10 : metricReturn discountingChainMetrics ≡ 10
check-discountingChain-return-x10 = refl
check-discountingChain-regret-x10 : metricRegret discountingChainMetrics ≡ 1
check-discountingChain-regret-x10 = refl
check-discountingChain-success : metricSuccess discountingChainMetrics ≡ 1
check-discountingChain-success = refl

check-rockSample-return : metricReturn rockSampleMetrics ≡ 0
check-rockSample-return = refl
check-rockSample-regret : metricRegret rockSampleMetrics ≡ 1
check-rockSample-regret = refl
check-rockSample-success : metricSuccess rockSampleMetrics ≡ 0
check-rockSample-success = refl

closedLoopBench-no-extra-action-source : ∀ (s : FullLearnerState) →
  canonicalBinaryAction s ≡ lift2 s
closedLoopBench-no-extra-action-source s = refl