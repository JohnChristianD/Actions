{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalLearnerGameExecution_test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (fromℕ<)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalGamePorts

learnerWatkinsKernel : WatkinsKernel
learnerWatkinsKernel = mkWatkinsKernel
  (λ q r → criticState (int8Add (qLeft q) r) (qRight q))
  (λ q r → disabled)
  (λ t g → g)

learnerAttentionStep : LearnedSparsemaxAttention → Int8 → LearnedSparsemaxAttention
learnerAttentionStep a r = a

learnerAttentionToGRU : WalshVec4 → Int8
learnerAttentionToGRU w = zero8

learnerOptimizerKernel : F4IntUKernel
learnerOptimizerKernel = f4IntUKernel zero8

learnerLCBKernel : LCBCountKernel
learnerLCBKernel = lcbCountKernel finiteLCBBonus8

learnerKernel : FullLearnerKernel
learnerKernel = mkFullLearnerKernel
  learnerWatkinsKernel
  learnerAttentionStep
  learnerAttentionToGRU
  learnerOptimizerKernel
  learnerLCBKernel

learnerInitial : FullLearnerState
learnerInitial = fullLearnerState
  zero
  (watkinsState (criticState zero8 zero8) zero8 disabled)
  identityAttention
  (gruState zero8 identityGRUMatrices zeroGRUNoise zeroGlobalControl)
  (f4IntUState zero8 zero8 zero8 zero8 zero8)
  (normPair zero8 zero8)
  (lcbCountState zero zero zero)
  canonicalQLogControl
  (finiteRational 0 1 1)

injectReward : FullLearnerState → Int8 → FullLearnerState
injectReward s r = fullLearnerState
  (clock s)
  (watkinsState (critic (watkins s)) r (trace (watkins s)))
  (attention s) (gru s) (optimizer s) (norm s) (lcbCounts s)
  (qLogControl s) (qLogValue s)

learnerRewardStep : FullLearnerState → Int8 → FullLearnerState
learnerRewardStep s r = canonicalFullStep learnerKernel (injectReward s r)

learnerRewardStep-clock : ∀ s r → clock (learnerRewardStep s r) ≡ suc (clock s)
learnerRewardStep-clock s r = canonicalFullStep-clock learnerKernel (injectReward s r)

knapsackRun : StepResult KnapsackState → FullLearnerState
knapsackRun e = learnerRewardStep learnerInitial (StepResult.reward e)

mazeRun : StepResult MazeState → FullLearnerState
mazeRun e = learnerRewardStep learnerInitial (StepResult.reward e)

lbfRun : StepResult LBFState → FullLearnerState
lbfRun e = learnerRewardStep learnerInitial (StepResult.reward e)

metaMazeRun : StepResult MetaMazeState → FullLearnerState
metaMazeRun e = learnerRewardStep learnerInitial (StepResult.reward e)

fourRoomsRun : StepResult MazeState → FullLearnerState
fourRoomsRun e = learnerRewardStep learnerInitial (StepResult.reward e)

pongRun : StepResult PongState → FullLearnerState
pongRun e = learnerRewardStep learnerInitial (StepResult.reward e)

memoryChainRun : StepResult MemoryChainState → FullLearnerState
memoryChainRun e = learnerRewardStep learnerInitial (StepResult.reward e)

discountingChainRun : StepResult DiscountingChainState → FullLearnerState
discountingChainRun e = learnerRewardStep learnerInitial (StepResult.reward e)

cartPoleRun : StepResult CartPoleQuantizedState → FullLearnerState
cartPoleRun e = learnerRewardStep learnerInitial (StepResult.reward e)

banditRun : StepResult BernoulliBanditState → FullLearnerState
banditRun e = learnerRewardStep learnerInitial (StepResult.reward e)

rockSampleRun : StepResult RockSampleState → FullLearnerState
rockSampleRun e = learnerRewardStep learnerInitial (StepResult.reward e)

check-knapsack : clock (knapsackRun (knapsackStep takeTake (knapsackState zero 8 zero))) ≡ 1
check-knapsack = refl

check-maze : clock (mazeRun (mazeStep (fromℕ< (m%n<n 1 4)) (mazeState 0 0 0 4 0))) ≡ 1
check-maze = refl

check-lbf : clock (lbfRun (lbfStep (fromℕ< (m%n<n 4 6)) (lbfState 0 0 0 1 0 1 1 0))) ≡ 1
check-lbf = refl

check-meta-maze : clock (metaMazeRun (metaMazeStep (fromℕ< (m%n<n 1 4)) (metaMazeState 0 0 0 4 0))) ≡ 1
check-meta-maze = refl

check-four-rooms : clock (fourRoomsRun (fourRoomsStep (fromℕ< (m%n<n 1 4)) (mazeState 4 1 8 9 0))) ≡ 1
check-four-rooms = refl

check-pong : clock (pongRun (pongStep (fromℕ< (m%n<n 1 3)) (pongState 4 4 2 2 1 1 0))) ≡ 1
check-pong = refl

check-memory-chain : clock (memoryChainRun (memoryChainStep (fromℕ< (m%n<n 0 2)) (memoryChainState 1 0 0))) ≡ 1
check-memory-chain = refl

check-discounting-chain : clock (discountingChainRun (discountingChainStep (fromℕ< (m%n<n 0 5)) (discountingChainState 0 0))) ≡ 1
check-discounting-chain = refl

check-cartpole : clock (cartPoleRun (cartPoleQuantizedStep (fromℕ< (m%n<n 1 2)) (cartPoleQuantizedState 1 0 0 0 0))) ≡ 1
check-cartpole = refl

check-bandit : clock (banditRun (bernoulliBanditStep (fromℕ< (m%n<n 0 2)) (bernoulliBanditState 0 0 0 0))) ≡ 1
check-bandit = refl

check-rocksample : clock (rockSampleRun (rockSampleStep (fromℕ< (m%n<n 4 6)) (rockSampleState 0 0 1 0))) ≡ 1
check-rocksample = refl
