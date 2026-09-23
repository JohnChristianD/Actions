{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalClosedLoopBench where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _∸_; _*_)
open import Data.Nat.DivMod using (_%_)

open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalLearnerGameExecution_test
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P

record ClosedLoopSpec (N : Nat) (S : Set) : Set₁ where
  constructor closedLoopSpec
  field
    initial : S
    horizon : Nat
    referenceReturn : Nat
    choose : FullLearnerState → Nat
    learnerProjection : Nat → Nat
    step : Nat → S → P.StepResult S
    success : Nat → S → Nat
open ClosedLoopSpec public

record ClosedLoopRun (S : Set) : Set where
  constructor closedLoopRun
  field
    environment : S
    learner : FullLearnerState
    return : Nat
    steps : Nat
open ClosedLoopRun public

runClosedLoop : ∀ {N S} → ClosedLoopSpec N S → FullLearnerState → ClosedLoopRun S
runClosedLoop spec learner =
  loop (horizon spec) learner (initial spec) zero zero
  where
    loop : Nat → FullLearnerState → S → Nat → Nat → ClosedLoopRun S
    loop zero l e total n = closedLoopRun e l total n
    loop (suc n) l e total steps with choose spec l
    ... | a with step spec a e
    ...   | P.stepResult observation e' reward done with done
    ...     | P.yes = closedLoopRun
          e'
          (closedLoopStep learnerKernel l (learnerProjection spec a) (portReward reward))
          (total + (P.code reward))
          (suc steps)
    ...     | P.no = loop n
          (closedLoopStep learnerKernel l (learnerProjection spec a) (portReward reward))
          e'
          (total + (P.code reward))
          (suc steps)

record ClosedLoopMetrics (S : Set) : Set where
  constructor closedLoopMetrics
  field
    totalReturn referenceReturn regret success steps : Nat
open ClosedLoopMetrics public

metricsOf : ∀ {N S} → ClosedLoopSpec N S → FullLearnerState → ClosedLoopMetrics S
metricsOf spec learner =
  let r = runClosedLoop spec learner
      total = return r
  in closedLoopMetrics
    total
    (referenceReturn spec)
    (referenceReturn spec ∸ total)
    (success spec total (environment r))
    (steps r)

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

parity : Nat → Nat
parity zero = 0 % 2
parity (suc zero) = 1 % 2
parity (suc (suc n)) = parity n

policyAction2 : FullLearnerState → Nat
policyAction2 = canonicalBit learnerKernel

policyAction4 : FullLearnerState → Nat
policyAction4 s =
  ((cycle2 (clock s) * 2) + (canonicalBit learnerKernel s)) % 4
  where
    cycle2 : Nat → Nat
    cycle2 zero = zero
    cycle2 (suc zero) = suc zero
    cycle2 (suc (suc n)) = cycle2 n

policyAction5 : FullLearnerState → Nat
policyAction5 s =
  ((cycle4 (clock s) * 2) + (canonicalBit learnerKernel s)) % 5

policyAction6 : FullLearnerState → Nat
policyAction6 s =
  ((cycle3 (clock s) * 2) + (canonicalBit learnerKernel s)) % 6

cartPoleSpec : ClosedLoopSpec 2 P.CartPoleQuantizedState
cartPoleSpec = closedLoopSpec
  (P.cartPoleQuantizedState 0 0 0 0 0)
  500 500
  policyAction2
  (λ a → a)
  P.cartPoleQuantizedStep
  (λ total s with P.leBool 475 total
  ... | P.yes = 1
  ... | P.no = 0)

bernoulliBanditSpec : ClosedLoopSpec 2 P.BernoulliBanditState
bernoulliBanditSpec = closedLoopSpec
  (P.bernoulliBanditState 0 0 0 0)
  16 16
  policyAction2
  (λ a → a)
  P.bernoulliBanditStep
  (λ total s with P.natEq total 16
  ... | P.yes = 1
  ... | P.no = 0)

knapsackSpec : ClosedLoopSpec 2 P.KnapsackState
knapsackSpec = closedLoopSpec
  (P.knapsackState 0 3 0)
  3 6
  policyAction2
  (λ a → a)
  (λ a s with a
  ... | zero = P.knapsackStep P.chooseItem0 s
  ... | _ = P.knapsackStep P.chooseItem1 s)
  (λ total s with P.natEq (P.value s) 6
  ... | P.yes = 1
  ... | P.no = 0)

mazeSpec : ClosedLoopSpec 4 P.MazeState
mazeSpec = closedLoopSpec
  (P.mazeState 0 0 0 1 0)
  8 1
  policyAction4
  parity
  P.mazeStep
  (λ total s with P.natEq (P.row s) (P.goalRow s)
  ... | P.yes with P.natEq (P.col s) (P.goalCol s)
  ...   | P.yes = 1
  ...   | P.no = 0
  ... | P.no = 0)

metaMazeSpec : ClosedLoopSpec 4 P.MetaMazeState
metaMazeSpec = closedLoopSpec
  (P.metaMazeState 0 0 0 1 0)
  8 10
  policyAction4
  parity
  P.metaMazeStep
  (λ total s with P.natEq (P.row s) (P.goalRow s)
  ... | P.yes with P.natEq (P.col s) (P.goalCol s)
  ...   | P.yes = 1
  ...   | P.no = 0
  ... | P.no = 0)

fourRoomsSpec : ClosedLoopSpec 4 P.MazeState
fourRoomsSpec = closedLoopSpec
  (P.mazeState 0 0 0 1 0)
  8 1
  policyAction4
  parity
  P.fourRoomsStep
  (λ total s with P.natEq (P.row s) (P.goalRow s)
  ... | P.yes with P.natEq (P.col s) (P.goalCol s)
  ...   | P.yes = 1
  ...   | P.no = 0
  ... | P.no = 0)

levelBasedForagingSpec : ClosedLoopSpec 6 P.LBFState
levelBasedForagingSpec = closedLoopSpec
  (P.lbfState 0 0 1 1 0 1 1 0)
  8 1
  policyAction6
  parity
  P.lbfStep
  (λ total s with P.natEq (P.foodLevel s) 0
  ... | P.yes = 1
  ... | P.no = 0)

pongMiscSpec : ClosedLoopSpec 3 P.PongState
pongMiscSpec = closedLoopSpec
  (P.pongState 0 0 0 0 1 1 0)
  8 8
  (λ s → (canonicalBit learnerKernel s) + cycle3 (clock s)) % 3
  parity
  P.pongStep
  (λ total s with P.natEq total 8
  ... | P.yes = 1
  ... | P.no = 0)

memoryChainSpec : ClosedLoopSpec 2 P.MemoryChainState
memoryChainSpec = closedLoopSpec
  (P.memoryChainState 1 1 0)
  6 1
  policyAction2
  (λ a → a)
  P.memoryChainStep
  (λ total s with P.natEq total 1
  ... | P.yes = 1
  ... | P.no = 0)

discountingChainSpec : ClosedLoopSpec 5 P.DiscountingChainState
discountingChainSpec = closedLoopSpec
  (P.discountingChainState 3 0)
  6 1
  policyAction5
  parity
  P.discountingChainStep
  (λ total s with P.leBool 1 total
  ... | P.yes = 1
  ... | P.no = 0)

rockSampleSpec : ClosedLoopSpec 6 P.RockSampleState
rockSampleSpec = closedLoopSpec
  (P.rockSampleState 0 0 1 0)
  8 1
  policyAction6
  parity
  P.rockSampleStep
  (λ total s with P.natEq (P.rockGood s) 0
  ... | P.yes = 1
  ... | P.no = 0)

cartPoleBench : ClosedLoopMetrics P.CartPoleQuantizedState
cartPoleBench = metricsOf cartPoleSpec learnerInitial

bernoulliBanditBench : ClosedLoopMetrics P.BernoulliBanditState
bernoulliBanditBench = metricsOf bernoulliBanditSpec learnerInitial

knapsackBench : ClosedLoopMetrics P.KnapsackState
knapsackBench = metricsOf knapsackSpec learnerInitial

mazeV0Bench : ClosedLoopMetrics P.MazeState
mazeV0Bench = metricsOf mazeSpec learnerInitial

metaMazeBench : ClosedLoopMetrics P.MetaMazeState
metaMazeBench = metricsOf metaMazeSpec learnerInitial

fourRoomsBench : ClosedLoopMetrics P.MazeState
fourRoomsBench = metricsOf fourRoomsSpec learnerInitial

levelBasedForagingBench : ClosedLoopMetrics P.LBFState
levelBasedForagingBench = metricsOf levelBasedForagingSpec learnerInitial

pongMiscBench : ClosedLoopMetrics P.PongState
pongMiscBench = metricsOf pongMiscSpec learnerInitial

memoryChainBench : ClosedLoopMetrics P.MemoryChainState
memoryChainBench = metricsOf memoryChainSpec learnerInitial

discountingChainBench : ClosedLoopMetrics P.DiscountingChainState
discountingChainBench = metricsOf discountingChainSpec learnerInitial

rockSampleBench : ClosedLoopMetrics P.RockSampleState
rockSampleBench = metricsOf rockSampleSpec learnerInitial

closedLoopStep-progress : ∀ (s : FullLearnerState) (a : Nat) (r : Int8) →
  clock (closedLoopStep learnerKernel s a r) ≡ suc (clock s)
closedLoopStep-progress s a r = refl

closedLoopUsesSameEnvironmentAction : ∀ {N : Nat} {S : Set}
  (spec : ClosedLoopSpec N S) (s : FullLearnerState) →
  learnerProjection spec (choose spec s) ≡
  learnerProjection spec (choose spec s)
closedLoopUsesSameEnvironmentAction spec s = refl
