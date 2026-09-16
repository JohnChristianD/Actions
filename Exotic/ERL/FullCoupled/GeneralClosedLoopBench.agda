{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.GeneralClosedLoopBench where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _∸_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat.DivMod using (m%n<n)

open import Exotic.ERL.FullCoupled.GeneralActionLearnerMonolith as L
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P

record LoopResult : Set where
  constructor loopResult
  field return regret success steps : Nat
open LoopResult public

initialState : ∀ {A : Nat} → Fin A → L.GeneralState A
initialState a = L.generalState zero L.zeroQ L.zeroCounts L.zeroGRU a

runLoop : ∀ {State Action A : Set} →
  (Fin A → Action) →
  (Action → State → P.StepResult State) →
  L.GeneralKernel A →
  L.GeneralState A →
  State →
  Nat →
  Nat →
  LoopResult
runLoop decode step K ls es zero optimum = loopResult zero optimum zero zero
runLoop decode step K ls es (suc n) optimum with L.generalPolicy K ls
... | a with step (decode a) es
...   | P.stepResult _ es' r P.yes =
  let rr = P.code r
      ret = toℕ rr
  in loopResult ret (optimum ∸ ret) 1 1
...   | P.stepResult _ es' r P.no with runLoop decode step K (L.generalStep K ls r) es' n optimum
...     | loopResult ret reg sucFlag k =
  let current = toℕ (P.code r)
      total = current + ret
  in loopResult total (optimum ∸ total) sucFlag (suc k)

fin2Action : Fin 2 → Fin 2
fin2Action a = a

fin3Pong : Fin 3 → Fin 3
fin3Pong a = a

fin4Maze : Fin 4 → Fin 4
fin4Maze a = a

fin6LBF : Fin 6 → Fin 6
fin6LBF a = a

fin5Discount : Fin 5 → Fin 5
fin5Discount a = a

decodeKnapsack : Fin 2 → P.KnapsackAction
decodeKnapsack a with toℕ a
... | zero = P.chooseItem0
... | _ = P.chooseItem1

bandit-plain : LoopResult
bandit-plain = runLoop
  fin2Action P.bernoulliBanditStep
  (L.generalKernel L.noMunchausen)
  (initialState (fromℕ< (m%n<n 0 2)))
  (P.bernoulliBanditState 1 0 0 0)
  8 8

bandit-munchausen : LoopResult
bandit-munchausen = runLoop
  fin2Action P.bernoulliBanditStep
  (L.generalKernel L.useMunchausen)
  (initialState (fromℕ< (m%n<n 0 2)))
  (P.bernoulliBanditState 1 0 0 0)
  8 8

cartpole-plain : LoopResult
cartpole-plain = runLoop
  fin2Action P.cartPoleQuantizedStep
  (L.generalKernel L.noMunchausen)
  (initialState (fromℕ< (m%n<n 0 2)))
  (P.cartPoleQuantizedState 1 0 0 0 0)
  8 0

cartpole-munchausen : LoopResult
cartpole-munchausen = runLoop
  fin2Action P.cartPoleQuantizedStep
  (L.generalKernel L.useMunchausen)
  (initialState (fromℕ< (m%n<n 0 2)))
  (P.cartPoleQuantizedState 1 0 0 0 0)
  8 0

maze-plain : LoopResult
maze-plain = runLoop
  fin4Maze P.mazeStep
  (L.generalKernel L.noMunchausen)
  (initialState (fromℕ< (m%n<n 0 4)))
  (P.mazeState 0 0 0 4 0)
  8 1

maze-munchausen : LoopResult
maze-munchausen = runLoop
  fin4Maze P.mazeStep
  (L.generalKernel L.useMunchausen)
  (initialState (fromℕ< (m%n<n 0 4)))
  (P.mazeState 0 0 0 4 0)
  8 1

metaMaze-plain : LoopResult
metaMaze-plain = runLoop
  fin4Maze P.metaMazeStep
  (L.generalKernel L.noMunchausen)
  (initialState (fromℕ< (m%n<n 0 4)))
  (P.metaMazeState 0 0 0 4 0)
  8 10

metaMaze-munchausen : LoopResult
metaMaze-munchausen = runLoop
  fin4Maze P.metaMazeStep
  (L.generalKernel L.useMunchausen)
  (initialState (fromℕ< (m%n<n 0 4)))
  (P.metaMazeState 0 0 0 4 0)
  8 10

fourRooms-plain : LoopResult
fourRooms-plain = runLoop
  fin4Maze P.fourRoomsStep
  (L.generalKernel L.noMunchausen)
  (initialState (fromℕ< (m%n<n 0 4)))
  (P.mazeState 4 1 8 9 0)
  8 1

fourRooms-munchausen : LoopResult
fourRooms-munchausen = runLoop
  fin4Maze P.fourRoomsStep
  (L.generalKernel L.useMunchausen)
  (initialState (fromℕ< (m%n<n 0 4)))
  (P.mazeState 4 1 8 9 0)
  8 1

knapsack-plain : LoopResult
knapsack-plain = runLoop
  decodeKnapsack P.knapsackStep
  (L.generalKernel L.noMunchausen)
  (initialState (fromℕ< (m%n<n 0 2)))
  (P.knapsackState 0 8 0)
  8 32

knapsack-munchausen : LoopResult
knapsack-munchausen = runLoop
  decodeKnapsack P.knapsackStep
  (L.generalKernel L.useMunchausen)
  (initialState (fromℕ< (m%n<n 0 2)))
  (P.knapsackState 0 8 0)
  8 32

lbf-plain : LoopResult
lbf-plain = runLoop
  fin6LBF P.lbfStep
  (L.generalKernel L.noMunchausen)
  (initialState (fromℕ< (m%n<n 0 6)))
  (P.lbfState 0 0 0 1 0 1 1 0)
  8 1

lbf-munchausen : LoopResult
lbf-munchausen = runLoop
  fin6LBF P.lbfStep
  (L.generalKernel L.useMunchausen)
  (initialState (fromℕ< (m%n<n 0 6)))
  (P.lbfState 0 0 0 1 0 1 1 0)
  8 1

pong-plain : LoopResult
pong-plain = runLoop
  fin3Pong P.pongStep
  (L.generalKernel L.noMunchausen)
  (initialState (fromℕ< (m%n<n 0 3)))
  (P.pongState 4 4 2 2 1 1 0)
  8 8

pong-munchausen : LoopResult
pong-munchausen = runLoop
  fin3Pong P.pongStep
  (L.generalKernel L.useMunchausen)
  (initialState (fromℕ< (m%n<n 0 3)))
  (P.pongState 4 4 2 2 1 1 0)
  8 8

memoryChain-plain : LoopResult
memoryChain-plain = runLoop
  fin2Action P.memoryChainStep
  (L.generalKernel L.noMunchausen)
  (initialState (fromℕ< (m%n<n 0 2)))
  (P.memoryChainState 1 0 0)
  8 1

memoryChain-munchausen : LoopResult
memoryChain-munchausen = runLoop
  fin2Action P.memoryChainStep
  (L.generalKernel L.useMunchausen)
  (initialState (fromℕ< (m%n<n 0 2)))
  (P.memoryChainState 1 0 0)
  8 1

discountingChain-plain : LoopResult
discountingChain-plain = runLoop
  fin5Discount P.discountingChainStep
  (L.generalKernel L.noMunchausen)
  (initialState (fromℕ< (m%n<n 0 5)))
  (P.discountingChainState 0 0)
  8 1

discountingChain-munchausen : LoopResult
discountingChain-munchausen = runLoop
  fin5Discount P.discountingChainStep
  (L.generalKernel L.useMunchausen)
  (initialState (fromℕ< (m%n<n 0 5)))
  (P.discountingChainState 0 0)
  8 1

rockSample-plain : LoopResult
rockSample-plain = runLoop
  fin6LBF P.rockSampleStep
  (L.generalKernel L.noMunchausen)
  (initialState (fromℕ< (m%n<n 0 6)))
  (P.rockSampleState 0 0 1 0)
  8 255

rockSample-munchausen : LoopResult
rockSample-munchausen = runLoop
  fin6LBF P.rockSampleStep
  (L.generalKernel L.useMunchausen)
  (initialState (fromℕ< (m%n<n 0 6)))
  (P.rockSampleState 0 0 1 0)
  8 255

metaMaze-closed-loop-law : steps metaMaze-plain ≡ 8
metaMaze-closed-loop-law = refl
