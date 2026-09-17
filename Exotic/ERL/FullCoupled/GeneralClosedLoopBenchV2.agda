{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GeneralClosedLoopBenchV2 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _∸_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat.DivMod using (m%n<n)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P
open import Exotic.ERL.FullCoupled.AdditionalBenchmarkPorts as B

record LoopResult : Set where
  constructor loopResult
  field return success steps distinctActions : Nat
open LoopResult public

record BenchEnv (A : Nat) (S : Set) : Set where
  constructor benchEnv
  field actionSpace : L.ActionSpace A
        initialState : S
        referenceReturn : Nat
        stepEnv : Fin A → S → P.StepResult S
open BenchEnv public

rewardL : P.Int8 → L.Int8
rewardL r = L.int8OfNat (toℕ (P.code r))

markAction : ∀ {A} → Fin A → L.CountVec A → L.CountVec A
markAction c a = L.incAt c a

runLoopAux : ∀ {A S} →
  BenchEnv A S → L.LearnerKernel A → Nat → L.LearnerState A → S → Nat → Nat → Nat → L.CountVec A → LoopResult
runLoopAux E K zero ls es total steps success seen =
  loopResult total success steps (countDistinct seen)
  where
    countDistinct : ∀ {A} → L.CountVec A → Nat
    countDistinct {A} c = countDistinctFin (L.finList A) c
    countDistinctFin : ∀ {A} → L.List (Fin A) → L.CountVec A → Nat
    countDistinctFin L.nil c = zero
    countDistinctFin (a L.:: as) c with L.natEq (c a) zero
    ... | L.yes = countDistinctFin as c
    ... | L.no = suc (countDistinctFin as c)
runLoopAux E K (suc n) ls es total steps success seen with L.generalPolicy K ls
... | a with stepEnv E a es
...   | P.stepResult obs es' r P.yes =
  let total' = total + toℕ (P.code r)
  in loopResult total' 1 (suc steps)
       (countDistinct (markAction a seen))
  where
    countDistinct : ∀ {A} → L.CountVec A → Nat
    countDistinct {A} c = countDistinctFin (L.finList A) c
    countDistinctFin : ∀ {A} → L.List (Fin A) → L.CountVec A → Nat
    countDistinctFin L.nil c = zero
    countDistinctFin (a L.:: as) c with L.natEq (c a) zero
    ... | L.yes = countDistinctFin as c
    ... | L.no = suc (countDistinctFin as c)
...   | P.stepResult obs es' r P.no =
  runLoopAux
    E K n
    (L.learnerStep K ls (rewardL r))
    es'
    (total + toℕ (P.code r))
    (suc steps)
    success
    (markAction a seen)

runLoop : ∀ {A S} → BenchEnv A S → L.LearnerKernel A → Nat → LoopResult
runLoop E K h =
  runLoopAux E K h
    (L.initialLearner (actionSpace E))
    (initialState E)
    zero zero zero (L.zeroCounts {A = _})

record AblationPair : Set where
  constructor ablationPair
  field plain munchausen : LoopResult
open AblationPair public

mkAblation : ∀ {A S} → BenchEnv A S → Nat → AblationPair
mkAblation E h =
  ablationPair
    (runLoop E (L.learnerKernel (actionSpace E) L.noMunchausen) h)
    (runLoop E (L.learnerKernel (actionSpace E) L.munchausen) h)

knapsackEnv : BenchEnv 2 P.KnapsackState
knapsackEnv = benchEnv
  L.actionSpace2
  (P.knapsackState 0 8 0)
  16
  (λ a s → P.knapsackStep (choose a) s)
  where
    choose : Fin 2 → P.KnapsackAction
    choose a with toℕ a
    ... | zero = P.chooseItem0
    ... | _ = P.chooseItem1

metaMazeEnv : BenchEnv 4 P.MetaMazeState
metaMazeEnv = benchEnv L.actionSpace4 (P.metaMazeState 0 0 0 4 0) 10 P.metaMazeStep

fourRoomsEnv : BenchEnv 4 P.MazeState
fourRoomsEnv = benchEnv L.actionSpace4 (P.mazeState 4 1 8 9 0) 1 P.fourRoomsStep

cartPoleEnv : BenchEnv 2 P.CartPoleQuantizedState
cartPoleEnv = benchEnv L.actionSpace2 (P.cartPoleQuantizedState 0 0 0 0 0) 500 P.cartPoleQuantizedStep

bernoulliBanditEnv : BenchEnv 2 P.BernoulliBanditState
bernoulliBanditEnv = benchEnv L.actionSpace2 (P.bernoulliBanditState 0 0 0 0) 90 P.bernoulliBanditStep

lbfEnv : BenchEnv 6 P.LBFState
lbfEnv = benchEnv
  (L.actionSpace (fromℕ< (m%n<n 0 6)))
  (P.lbfState 0 0 0 1 0 1 1 0)
  1 P.lbfStep

pongEnv : BenchEnv 3 P.PongState
pongEnv = benchEnv
  (L.actionSpace (fromℕ< (m%n<n 0 3)))
  (P.pongState 4 4 2 2 1 1 0)
  8 P.pongStep

memoryChainEnv : BenchEnv 2 P.MemoryChainState
memoryChainEnv = benchEnv L.actionSpace2 (P.memoryChainState 1 0 0) 1 P.memoryChainStep

discountingChainEnv : BenchEnv 5 P.DiscountingChainState
discountingChainEnv = benchEnv
  (L.actionSpace (fromℕ< (m%n<n 0 5)))
  (P.discountingChainState 0 0)
  1 P.discountingChainStep

pobaxTMazeEnv : BenchEnv 3 B.TMazeState
pobaxTMazeEnv = benchEnv
  (L.actionSpace (fromℕ< (m%n<n 0 3)))
  B.tMazeInitial
  1 B.tMazeStep

uniformGaussianBanditEnv : BenchEnv 2 B.UniformBanditState
uniformGaussianBanditEnv = benchEnv
  L.actionSpace2 B.uniformBanditInitial 16 B.uniformBanditStep

game2048Env : BenchEnv 4 B.Game2048State
game2048Env = benchEnv
  L.actionSpace4 B.game2048Initial 32 B.game2048Step

knapsackAblation : AblationPair
knapsackAblation = mkAblation knapsackEnv 16

metaMazeAblation : AblationPair
metaMazeAblation = mkAblation metaMazeEnv 32

fourRoomsAblation : AblationPair
fourRoomsAblation = mkAblation fourRoomsEnv 32

cartPoleAblation : AblationPair
cartPoleAblation = mkAblation cartPoleEnv 16

bernoulliBanditAblation : AblationPair
bernoulliBanditAblation = mkAblation bernoulliBanditEnv 16

lbfAblation : AblationPair
lbfAblation = mkAblation lbfEnv 16

pongAblation : AblationPair
pongAblation = mkAblation pongEnv 16

memoryChainAblation : AblationPair
memoryChainAblation = mkAblation memoryChainEnv 16

discountingChainAblation : AblationPair
discountingChainAblation = mkAblation discountingChainEnv 16

pobaxTMazeAblation : AblationPair
pobaxTMazeAblation = mkAblation pobaxTMazeEnv 8

uniformGaussianBanditAblation : AblationPair
uniformGaussianBanditAblation = mkAblation uniformGaussianBanditEnv 16

game2048Ablation : AblationPair
game2048Ablation = mkAblation game2048Env 32
