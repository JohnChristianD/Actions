{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalGeneralClosedLoopBench where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _∸_; _+_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat.DivMod using (m%n<n)

open import Exotic.ERL.FullCoupled.CanonicalGeneralLearnerMonolith as L
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P

record BenchMetrics : Set where
  constructor benchMetrics
  field return regret success steps : Nat
open BenchMetrics public

record AblationMetrics : Set where
  constructor ablationMetrics
  field plain munchausen : BenchMetrics
open AblationMetrics public

record GeneralEnv (A : Nat) (S : Set) : Set₁ where
  constructor generalEnv
  field step : Fin A → S → P.StepResult S
open GeneralEnv public

record GeneralBenchSpec (A : Nat) (S : Set) : Set₁ where
  constructor generalBenchSpec
  field
    environment : GeneralEnv A S
    initialEnvironment : S
    initialLearner : L.GeneralLearnerState A
    horizon referenceReturn : Nat
    success : S → Nat
open GeneralBenchSpec public

runAux : ∀ {S : Set} {N : Nat} →
  GeneralBenchSpec N S →
  L.GeneralLearnerKernel N →
  Nat → L.GeneralLearnerState N → S → Nat → Nat → BenchMetrics
runAux spec K zero learner env total steps =
  benchMetrics total (referenceReturn spec ∸ total) (success spec env) steps
runAux spec K (suc n) learner env total steps with L.policyA K learner
... | a with step (environment spec) a env
...   | P.stepResult observation env' reward P.enabled =
      benchMetrics
        (total + toℕ (P.code reward))
        (referenceReturn spec ∸ (total + toℕ (P.code reward)))
        (success spec env')
        (suc steps)
...   | P.stepResult observation env' reward P.disabled =
      runAux spec K n
        (L.generalLearnerStep K learner reward)
        env'
        (total + toℕ (P.code reward))
        (suc steps)

runPlain : ∀ {S : Set} {N : Nat} → GeneralBenchSpec N S → BenchMetrics
runPlain spec = runAux spec
  (L.generalLearnerKernel L.noMunchausen (L.f4IntUKernel L.zero8))
  (horizon spec)
  (initialLearner spec)
  (initialEnvironment spec)
  zero zero

runMunchausen : ∀ {S : Set} {N : Nat} → GeneralBenchSpec N S → BenchMetrics
runMunchausen spec = runAux spec
  (L.generalLearnerKernel L.useMunchausen (L.f4IntUKernel L.zero8))
  (horizon spec)
  (initialLearner spec)
  (initialEnvironment spec)
  zero zero

runAblation : ∀ {S : Set} {N : Nat} → GeneralBenchSpec N S → AblationMetrics
runAblation spec = ablationMetrics (runPlain spec) (runMunchausen spec)

initialGeneral : ∀ {A : Nat} → Fin A → L.GeneralLearnerState A
initialGeneral a = L.generalLearnerState
  zero L.zeroQ L.zeroCounts L.zeroAttention L.zeroGRU
  (L.f4IntUState L.zero8 L.zero8 L.zero8 L.zero8 L.zero8)
  (L.normPair L.zero8 L.zero8) L.zero8 a

arities-2 : Nat
arities-2 = 2
arities-3 : Nat
arities-3 = 3
arities-4 : Nat
arities-4 = 4
arities-5 : Nat
arities-5 = 5
arities-6 : Nat
arities-6 = 6

decodeKnapsack : Fin 2 → P.KnapsackAction
decodeKnapsack a with toℕ a
... | zero = P.chooseItem0
... | _ = P.chooseItem1

knapsackSpec : GeneralBenchSpec 2 P.KnapsackState
knapsackSpec = generalBenchSpec
  (generalEnv (λ a s → P.knapsackStep (decodeKnapsack a) s))
  (P.knapsackState 0 3 0)
  (initialGeneral (P.fin2 0)) 3 6
  (λ s with P.natEq (P.value s) 6
  ... | P.enabled = 1
  ... | P.disabled = 0)

knapsackBench : AblationMetrics
knapsackBench = runAblation knapsackSpec

mazeSpec : GeneralBenchSpec 4 P.MazeState
mazeSpec = generalBenchSpec (generalEnv P.mazeStep)
  (P.mazeState 0 0 0 1 0) (initialGeneral (P.fin4 0)) 8 1
  (λ s with P.natEq (P.row s) (P.goalRow s)
  ... | P.enabled with P.natEq (P.col s) (P.goalCol s)
  ...   | P.enabled = 1
  ...   | P.disabled = 0
  ... | P.disabled = 0)

mazeBench : AblationMetrics
mazeBench = runAblation mazeSpec

metaMazeSpec : GeneralBenchSpec 4 P.MetaMazeState
metaMazeSpec = generalBenchSpec (generalEnv P.metaMazeStep)
  (P.metaMazeState 0 0 0 1 0) (initialGeneral (P.fin4 0)) 8 10
  (λ s with P.natEq (P.row s) (P.goalRow s)
  ... | P.enabled with P.natEq (P.col s) (P.goalCol s)
  ...   | P.enabled = 1
  ...   | P.disabled = 0
  ... | P.disabled = 0)

metaMazeBench : AblationMetrics
metaMazeBench = runAblation metaMazeSpec

fourRoomsSpec : GeneralBenchSpec 4 P.MazeState
fourRoomsSpec = generalBenchSpec (generalEnv P.fourRoomsStep)
  (P.mazeState 0 0 0 1 0) (initialGeneral (P.fin4 0)) 8 1
  (λ s with P.natEq (P.row s) (P.goalRow s)
  ... | P.enabled with P.natEq (P.col s) (P.goalCol s)
  ...   | P.enabled = 1
  ...   | P.disabled = 0
  ... | P.disabled = 0)

fourRoomsBench : AblationMetrics
fourRoomsBench = runAblation fourRoomsSpec

levelBasedForagingSpec : GeneralBenchSpec 6 P.LBFState
levelBasedForagingSpec = generalBenchSpec (generalEnv P.lbfStep)
  (P.lbfState 0 0 1 1 0 1 1 0) (initialGeneral (P.fin6 0)) 8 1
  (λ s with P.natEq (P.foodLevel s) 0
  ... | P.enabled = 1
  ... | P.disabled = 0)

levelBasedForagingBench : AblationMetrics
levelBasedForagingBench = runAblation levelBasedForagingSpec

pongSpec : GeneralBenchSpec 3 P.PongState
pongSpec = generalBenchSpec (generalEnv P.pongStep)
  (P.pongState 0 0 0 0 1 1 0) (initialGeneral (P.fin3 0)) 8 8
  (λ s → 1)

pongBench : AblationMetrics
pongBench = runAblation pongSpec

memoryChainSpec : GeneralBenchSpec 2 P.MemoryChainState
memoryChainSpec = generalBenchSpec (generalEnv P.memoryChainStep)
  (P.memoryChainState 1 1 0) (initialGeneral (P.fin2 0)) 6 1
  (λ s with P.natEq (P.time s) 1
  ... | P.enabled = 1
  ... | P.disabled = 0)

memoryChainBench : AblationMetrics
memoryChainBench = runAblation memoryChainSpec

discountingChainSpec : GeneralBenchSpec 5 P.DiscountingChainState
discountingChainSpec = generalBenchSpec (generalEnv P.discountingChainStep)
  (P.discountingChainState 3 0) (initialGeneral (P.fin5 0)) 6 5
  (λ s → 1)

discountingChainBench : AblationMetrics
discountingChainBench = runAblation discountingChainSpec

cartPoleSpec : GeneralBenchSpec 2 P.CartPoleQuantizedState
cartPoleSpec = generalBenchSpec (generalEnv P.cartPoleQuantizedStep)
  (P.cartPoleQuantizedState 0 0 0 0 0) (initialGeneral (P.fin2 0)) 8 0
  (λ s → 0)

cartPoleBench : AblationMetrics
cartPoleBench = runAblation cartPoleSpec

banditSpec : GeneralBenchSpec 2 P.BernoulliBanditState
banditSpec = generalBenchSpec (generalEnv P.bernoulliBanditStep)
  (P.bernoulliBanditState 1 0 0 0) (initialGeneral (P.fin2 0)) 8 8
  (λ s with P.natEq (P.lastReward s) 1
  ... | P.enabled = 1
  ... | P.disabled = 0)

banditBench : AblationMetrics
banditBench = runAblation banditSpec

rockSampleSpec : GeneralBenchSpec 6 P.RockSampleState
rockSampleSpec = generalBenchSpec (generalEnv P.rockSampleStep)
  (P.rockSampleState 0 0 1 0) (initialGeneral (P.fin6 0)) 8 1
  (λ s with P.natEq (P.rockGood s) 0
  ... | P.enabled = 1
  ... | P.disabled = 0)

rockSampleBench : AblationMetrics
rockSampleBench = runAblation rockSampleSpec

closedLoopStep-counts : ∀ {A : Nat} K s r →
  L.clock (L.generalLearnerStep K s r) ≡ suc (L.clock s)
closedLoopStep-counts = L.generalLearnerStep-clock

ablationSteps8 : ∀ {S : Set} {N : Nat} (B : GeneralBenchSpec N S) →
  steps (plain (runAblation B)) ≡ 8 →
  steps (munchausen (runAblation B)) ≡ 8
ablationSteps8 B p = p
