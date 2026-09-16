{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalLearnerGameExecution_test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (fromℕ<)
open import Data.Fin.DivMod using ()
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P

portReward : P.Int8 → Int8
portReward r = int8OfNat (P.Int8.code r |> toℕ)
  where
    _|>_ : Fin 256 → Nat
    x |> f = f x

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

knapsackRun : P.StepResult P.KnapsackState → FullLearnerState
knapsackRun e = learnerRewardStep learnerInitial (portReward (P.reward e))

mazeRun : P.StepResult P.MazeState → FullLearnerState
mazeRun e = learnerRewardStep learnerInitial (portReward (P.reward e))

lbfRun : P.StepResult P.LBFState → FullLearnerState
lbfRun e = learnerRewardStep learnerInitial (portReward (P.reward e))

metaMazeRun : P.StepResult P.MetaMazeState → FullLearnerState
metaMazeRun e = learnerRewardStep learnerInitial (portReward (P.reward e))

fourRoomsRun : P.StepResult P.MazeState → FullLearnerState
fourRoomsRun e = learnerRewardStep learnerInitial (portReward (P.reward e))

pongRun : P.StepResult P.PongState → FullLearnerState
pongRun e = learnerRewardStep learnerInitial (portReward (P.reward e))

memoryChainRun : P.StepResult P.MemoryChainState → FullLearnerState
memoryChainRun e = learnerRewardStep learnerInitial (portReward (P.reward e))

discountingChainRun : P.StepResult P.DiscountingChainState → FullLearnerState
discountingChainRun e = learnerRewardStep learnerInitial (portReward (P.reward e))

cartPoleRun : P.StepResult P.CartPoleQuantizedState → FullLearnerState
cartPoleRun e = learnerRewardStep learnerInitial (portReward (P.reward e))

banditRun : P.StepResult P.BernoulliBanditState → FullLearnerState
banditRun e = learnerRewardStep learnerInitial (portReward (P.reward e))

rockSampleRun : P.StepResult P.RockSampleState → FullLearnerState
rockSampleRun e = learnerRewardStep learnerInitial (portReward (P.reward e))

check-knapsack : clock (knapsackRun (P.knapsackStep P.chooseItem0 (P.knapsackState 0 8 0))) ≡ 1
check-knapsack = refl

check-maze : clock (mazeRun (P.mazeStep (P.fin4 1) (P.mazeState 0 0 0 4 0))) ≡ 1
check-maze = refl

check-lbf : clock (lbfRun (P.lbfStep (P.fin6 4) (P.lbfState 0 0 0 1 0 1 1 0))) ≡ 1
check-lbf = refl

check-meta-maze : clock (metaMazeRun (P.metaMazeStep (P.fin4 1) (P.metaMazeState 0 0 0 4 0))) ≡ 1
check-meta-maze = refl

check-four-rooms : clock (fourRoomsRun (P.fourRoomsStep (P.fin4 1) (P.mazeState 4 1 8 9 0))) ≡ 1
check-four-rooms = refl

check-pong : clock (pongRun (P.pongStep (P.fin3 1) (P.pongState 4 4 2 2 1 1 0))) ≡ 1
check-pong = refl

check-memory-chain : clock (memoryChainRun (P.memoryChainStep (P.fin2 0) (P.memoryChainState 1 0 0))) ≡ 1
check-memory-chain = refl

check-discounting-chain : clock (discountingChainRun (P.discountingChainStep (P.fin5 0) (P.discountingChainState 0 0))) ≡ 1
check-discounting-chain = refl

check-cartpole : clock (cartPoleRun (P.cartPoleQuantizedStep (P.fin2 1) (P.cartPoleQuantizedState 1 0 0 0 0))) ≡ 1
check-cartpole = refl

check-bandit : clock (banditRun (P.bernoulliBanditStep (P.fin2 0) (P.bernoulliBanditState 0 0 0 0))) ≡ 1
check-bandit = refl

check-rocksample : clock (rockSampleRun (P.rockSampleStep (P.fin6 4) (P.rockSampleState 0 0 1 0))) ≡ 1
check-rocksample = refl
