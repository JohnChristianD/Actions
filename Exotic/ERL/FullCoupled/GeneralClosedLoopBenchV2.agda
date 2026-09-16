{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GeneralClosedLoopBenchV2 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _∸_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat.DivMod using (m%n<n)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P

record LoopResult : Set where
  constructor loopResult
  field return regret success steps : Nat
open LoopResult public

record BenchEnv (A : Nat) (S : Set) : Set where
  constructor benchEnv
  field actionSpace : L.ActionSpace A
        initial : S
        reference : Nat
        step : Fin A → S → P.StepResult S
open BenchEnv public

rewardL : P.Int8 → L.Int8
rewardL r = L.int8OfNat (toℕ (P.code r))

initialLearner : ∀ {A} → L.ActionSpace A → L.LearnerState A
initialLearner = L.initialLearner

runLoop : ∀ {A : Nat} {S : Set} →
  BenchEnv A S → L.LearnerKernel A → Nat → L.LearnerState A → S → Nat → LoopResult
runLoop E K zero ls es total = loopResult total (reference E ∸ total) 0 zero
runLoop E K (suc n) ls es total with L.generalPolicy K ls
... | a with step E a es
...   | P.stepResult obs es' r P.yes =
  let total' = total + toℕ (P.code r)
  in loopResult total' (reference E ∸ total') 1 (suc zero)
...   | P.stepResult obs es' r P.no =
  runLoop E K n (L.learnerStep K ls (rewardL r)) es' (total + toℕ (P.code r))

runBenchmark : ∀ {A : Nat} {S : Set} →
  BenchEnv A S → MunchausenModePair A → Nat → LoopResult × LoopResult
runBenchmark E K h =
  runPair E K h
  where
    runPair : ∀ {A : Nat} {S : Set} →
      BenchEnv A S → MunchausenModePair A → Nat → LoopResult × LoopResult
    runPair E K h =
      runLoop E (plainKernel E K) h (initialLearner (actionSpace E)) (initial E) zero
      , runLoop E (munchausenKernel E K) h (initialLearner (actionSpace E)) (initial E) zero

record MunchausenModePair (A : Nat) : Set where
  constructor modePair
  field actionSpacePair : L.ActionSpace A
open MunchausenModePair public

plainKernel : ∀ {A : Nat} {S : Set} → BenchEnv A S → MunchausenModePair A → L.LearnerKernel A
plainKernel E K = L.learnerKernel (actionSpacePair K) L.noMunchausen

munchausenKernel : ∀ {A : Nat} {S : Set} → BenchEnv A S → MunchausenModePair A → L.LearnerKernel A
munchausenKernel E K = L.learnerKernel (actionSpacePair K) L.munchausen

record AblationPair : Set where
  constructor ablationPair
  field plain munchausen : LoopResult
open AblationPair public

mkAblation : ∀ {A : Nat} {S : Set} → BenchEnv A S → L.LearnerKernel A → Nat → AblationPair
mkAblation E K h =
  let lp = runLoop E (L.learnerKernel (actionSpace E) L.noMunchausen) h (initialLearner (actionSpace E)) (initial E) zero
      lm = runLoop E (L.learnerKernel (actionSpace E) L.munchausen) h (initialLearner (actionSpace E)) (initial E) zero
  in ablationPair lp lm

knapsackEnv : BenchEnv 2 P.KnapsackState
knapsackEnv = benchEnv
  L.actionSpace2
  (P.knapsackState 0 8 0)
  16
  (λ a → λ s → P.knapsackStep (choose a) s)
  where
    choose a with toℕ a
    ... | zero = P.chooseItem0
    ... | _ = P.chooseItem1

mazeEnv : BenchEnv 4 P.MazeState
mazeEnv = benchEnv
  L.actionSpace4
  (P.mazeState 0 0 0 4 0)
  1
  P.mazeStep

metaMazeEnv : BenchEnv 4 P.MetaMazeState
metaMazeEnv = benchEnv
  L.actionSpace4
  (P.metaMazeState 0 0 0 4 0)
  10
  P.metaMazeStep

fourRoomsEnv : BenchEnv 4 P.MazeState
fourRoomsEnv = benchEnv
  L.actionSpace4
  (P.mazeState 4 1 8 9 0)
  1
  P.fourRoomsStep

cartPoleEnv : BenchEnv 2 P.CartPoleQuantizedState
cartPoleEnv = benchEnv
  L.actionSpace2
  (P.cartPoleQuantizedState 0 0 0 0 0)
  500
  P.cartPoleQuantizedStep

bernoulliBanditEnv : BenchEnv 2 P.BernoulliBanditState
bernoulliBanditEnv = benchEnv
  L.actionSpace2
  (P.bernoulliBanditState 0 0 0 0)
  90
  P.bernoulliBanditStep

lbfEnv : BenchEnv 6 P.LBFState
lbfEnv = benchEnv
  (L.actionSpace (fromℕ< (m%n<n 0 6)))
  (P.lbfState 0 0 0 1 0 1 1 0)
  1
  P.lbfStep

pongEnv : BenchEnv 3 P.PongState
pongEnv = benchEnv
  (L.actionSpace (fromℕ< (m%n<n 0 3)))
  (P.pongState 4 4 2 2 1 1 0)
  8
  P.pongStep

memoryChainEnv : BenchEnv 2 P.MemoryChainState
memoryChainEnv = benchEnv
  L.actionSpace2
  (P.memoryChainState 1 0 0)
  1
  P.memoryChainStep

discountingChainEnv : BenchEnv 5 P.DiscountingChainState
discountingChainEnv = benchEnv
  (L.actionSpace (fromℕ< (m%n<n 0 5)))
  (P.discountingChainState 0 0)
  1
  P.discountingChainStep

rockSampleEnv : BenchEnv 6 P.RockSampleState
rockSampleEnv = benchEnv
  (L.actionSpace (fromℕ< (m%n<n 0 6)))
  (P.rockSampleState 0 0 1 0)
  255
  P.rockSampleStep

banditAblation : AblationPair
banditAblation = mkAblation bernoulliBanditEnv (L.learnerKernel L.actionSpace2 L.noMunchausen) 16

cartPoleAblation : AblationPair
cartPoleAblation = mkAblation cartPoleEnv (L.learnerKernel L.actionSpace2 L.noMunchausen) 16

mazeAblation : AblationPair
mazeAblation = mkAblation mazeEnv (L.learnerKernel L.actionSpace4 L.noMunchausen) 32

metaMazeAblation : AblationPair
metaMazeAblation = mkAblation metaMazeEnv (L.learnerKernel L.actionSpace4 L.noMunchausen) 32

fourRoomsAblation : AblationPair
fourRoomsAblation = mkAblation fourRoomsEnv (L.learnerKernel L.actionSpace4 L.noMunchausen) 32

knapsackAblation : AblationPair
knapsackAblation = mkAblation knapsackEnv (L.learnerKernel L.actionSpace2 L.noMunchausen) 16

lbfAblation : AblationPair
lbfAblation = mkAblation lbfEnv (L.learnerKernel (L.actionSpace (fromℕ< (m%n<n 0 6))) L.noMunchausen) 16

pongAblation : AblationPair
pongAblation = mkAblation pongEnv (L.learnerKernel (L.actionSpace (fromℕ< (m%n<n 0 3))) L.noMunchausen) 16

memoryChainAblation : AblationPair
memoryChainAblation = mkAblation memoryChainEnv (L.learnerKernel L.actionSpace2 L.noMunchausen) 16

discountingChainAblation : AblationPair
discountingChainAblation = mkAblation discountingChainEnv (L.learnerKernel (L.actionSpace (fromℕ< (m%n<n 0 5))) L.noMunchausen) 16

rockSampleAblation : AblationPair
rockSampleAblation = mkAblation rockSampleEnv (L.learnerKernel (L.actionSpace (fromℕ< (m%n<n 0 6))) L.noMunchausen) 16

