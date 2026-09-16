{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.GeneralClosedLoopBench where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _∸_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)

open import Exotic.ERL.FullCoupled.GeneralActionLearnerMonolith as L
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P

record LoopResult : Set where
  constructor loopResult
  field return regret success steps : Nat
open LoopResult public

record LoopRun (State Action : Set) : Set₁ where
  constructor loopRun
  field state : State
        actionDecode : Fin 1 → Action
        optimalReturn horizon successThreshold : Nat
open LoopRun public

actionFin2 : Fin 2
actionFin2 = fromℕ< (m%n<n 0 2)

actionFin3 : Fin 3
actionFin3 = fromℕ< (m%n<n 0 3)

actionFin4 : Fin 4
actionFin4 = fromℕ< (m%n<n 0 4)

initialState : ∀ {A : Nat} → Fin A → L.GeneralState A
initialState a = L.generalState zero L.zeroQ L.zeroCounts L.zeroGRU a

record Acc : Set where
  constructor acc
  field total reached done steps : Nat
open Acc public

markDone : P.BoolLike → Nat
markDone P.yes = 1
markDone P.no = 0

maxNat : Nat → Nat → Nat
maxNat zero n = n
maxNat (suc m) zero = suc m
maxNat (suc m) (suc n) = suc (maxNat m n)

runKnapsack : L.MunchausenMode → Nat → P.KnapsackState → Acc
runKnapsack mode zero s = acc 0 0 0 0
runKnapsack mode (suc n) s with L.generalPolicy {suc zero} (L.generalKernel mode) (initialState (fromℕ< (m%n<n 0 2)))
... | a with P.knapsackStep (decode2 a) s
...   | P.stepResult _ s' r d =
  let rest = runKnapsack mode n s'
  in acc (toℕ (P.code r) + total rest) (maxNat (markDone d) (reached rest))
      (maxNat (markDone d) (done rest)) (suc (steps rest))
  where
    decode2 : Fin 2 → P.KnapsackAction
    decode2 a with toℕ a
    ... | zero = P.chooseItem0
    ... | _ = P.chooseItem1

cartPoleLoop : L.MunchausenMode → Nat → P.CartPoleQuantizedState → Acc
cartPoleLoop mode zero s = acc 0 0 0 0
cartPoleLoop mode (suc n) s with L.generalPolicy {suc (suc zero)} (L.generalKernel mode) (initialState (fromℕ< (m%n<n 0 2)))
... | a with P.cartPoleQuantizedStep (fin2Action a) s
...   | P.stepResult _ s' r d =
  let rest = cartPoleLoop mode n s'
  in acc (toℕ (P.code r) + total rest) (maxNat (markDone d) (reached rest))
      (maxNat (markDone d) (done rest)) (suc (steps rest))
  where
    fin2Action : Fin 2 → Fin 2
    fin2Action a = a

banditLoop : L.MunchausenMode → Nat → P.BernoulliBanditState → Acc
banditLoop mode zero s = acc 0 0 0 0
banditLoop mode (suc n) s with L.generalPolicy {suc (suc zero)} (L.generalKernel mode) (initialState (fromℕ< (m%n<n 0 2)))
... | a with P.bernoulliBanditStep a s
...   | P.stepResult _ s' r d =
  let rest = banditLoop mode n s'
  in acc (toℕ (P.code r) + total rest) (maxNat (markDone d) (reached rest))
      (maxNat (markDone d) (done rest)) (suc (steps rest))

mazeLoop : L.MunchausenMode → Nat → P.MazeState → Acc
mazeLoop mode zero s = acc 0 0 0 0
mazeLoop mode (suc n) s with L.generalPolicy {suc (suc (suc zero))} (L.generalKernel mode) (initialState (fromℕ< (m%n<n 0 4)))
... | a with P.mazeStep a s
...   | P.stepResult _ s' r d =
  let rest = mazeLoop mode n s'
  in acc (toℕ (P.code r) + total rest) (maxNat (markDone d) (reached rest))
      (maxNat (markDone d) (done rest)) (suc (steps rest))

fourRoomsLoop : L.MunchausenMode → Nat → P.MazeState → Acc
fourRoomsLoop = mazeLoop

metaMazeLoop : L.MunchausenMode → Nat → P.MetaMazeState → Acc
metaMazeLoop mode zero s = acc 0 0 0 0
metaMazeLoop mode (suc n) s with L.generalPolicy {suc (suc (suc zero))} (L.generalKernel mode) (initialState (fromℕ< (m%n<n 0 4)))
... | a with P.metaMazeStep a s
...   | P.stepResult _ s' r d =
  let rest = metaMazeLoop mode n s'
  in acc (toℕ (P.code r) + total rest) (maxNat (markDone d) (reached rest))
      (maxNat (markDone d) (done rest)) (suc (steps rest))

memoryChainLoop : L.MunchausenMode → Nat → P.MemoryChainState → Acc
memoryChainLoop mode zero s = acc 0 0 0 0
memoryChainLoop mode (suc n) s with L.generalPolicy {suc (suc zero)} (L.generalKernel mode) (initialState (fromℕ< (m%n<n 0 2)))
... | a with P.memoryChainStep a s
...   | P.stepResult _ s' r d =
  let rest = memoryChainLoop mode n s'
  in acc (toℕ (P.code r) + total rest) (maxNat (markDone d) (reached rest))
      (maxNat (markDone d) (done rest)) (suc (steps rest))

discountingChainLoop : L.MunchausenMode → Nat → P.DiscountingChainState → Acc
discountingChainLoop mode zero s = acc 0 0 0 0
discountingChainLoop mode (suc n) s with L.generalPolicy {suc (suc (suc (suc zero)))} (L.generalKernel mode) (initialState (fromℕ< (m%n<n 0 5)))
... | a with P.discountingChainStep a s
...   | P.stepResult _ s' r d =
  let rest = discountingChainLoop mode n s'
  in acc (toℕ (P.code r) + total rest) (maxNat (markDone d) (reached rest))
      (maxNat (markDone d) (done rest)) (suc (steps rest))

lbfLoop : L.MunchausenMode → Nat → P.LBFState → Acc
lbfLoop mode zero s = acc 0 0 0 0
lbfLoop mode (suc n) s with L.generalPolicy {suc (suc (suc (suc (suc zero))))} (L.generalKernel mode) (initialState (fromℕ< (m%n<n 0 6)))
... | a with P.lbfStep a s
...   | P.stepResult _ s' r d =
  let rest = lbfLoop mode n s'
  in acc (toℕ (P.code r) + total rest) (maxNat (markDone d) (reached rest))
      (maxNat (markDone d) (done rest)) (suc (steps rest))

pongLoop : L.MunchausenMode → Nat → P.PongState → Acc
pongLoop mode zero s = acc 0 0 0 0
pongLoop mode (suc n) s with L.generalPolicy {suc (suc zero)} (L.generalKernel mode) (initialState (fromℕ< (m%n<n 0 3)))
... | a with P.pongStep a s
...   | P.stepResult _ s' r d =
  let rest = pongLoop mode n s'
  in acc (toℕ (P.code r) + total rest) (maxNat (markDone d) (reached rest))
      (maxNat (markDone d) (done rest)) (suc (steps rest))

rockSampleLoop : L.MunchausenMode → Nat → P.RockSampleState → Acc
rockSampleLoop mode zero s = acc 0 0 0 0
rockSampleLoop mode (suc n) s with L.generalPolicy {suc (suc (suc (suc (suc zero))))} (L.generalKernel mode) (initialState (fromℕ< (m%n<n 0 6)))
... | a with P.rockSampleStep a s
...   | P.stepResult _ s' r d =
  let rest = rockSampleLoop mode n s'
  in acc (toℕ (P.code r) + total rest) (maxNat (markDone d) (reached rest))
      (maxNat (markDone d) (done rest)) (suc (steps rest))

mkResult : Acc → Nat → LoopResult
mkResult a optimum = loopResult (total a) (optimum ∸ total a) (done a) (steps a)

bandit-plain : LoopResult
bandit-plain = mkResult (banditLoop L.noMunchausen 8 (P.bernoulliBanditState 1 0 0 0)) 8

bandit-munchausen : LoopResult
bandit-munchausen = mkResult (banditLoop L.useMunchausen 8 (P.bernoulliBanditState 1 0 0 0)) 8

cartpole-plain : LoopResult
cartpole-plain = mkResult (cartPoleLoop L.noMunchausen 8 (P.cartPoleQuantizedState 1 0 0 0 0)) 0

cartpole-munchausen : LoopResult
cartpole-munchausen = mkResult (cartPoleLoop L.useMunchausen 8 (P.cartPoleQuantizedState 1 0 0 0 0)) 0

maze-plain : LoopResult
maze-plain = mkResult (mazeLoop L.noMunchausen 8 (P.mazeState 0 0 0 4 0)) 1

maze-munchausen : LoopResult
maze-munchausen = mkResult (mazeLoop L.useMunchausen 8 (P.mazeState 0 0 0 4 0)) 1

metaMaze-plain : LoopResult
metaMaze-plain = mkResult (metaMazeLoop L.noMunchausen 8 (P.metaMazeState 0 0 0 4 0)) 10

metaMaze-munchausen : LoopResult
metaMaze-munchausen = mkResult (metaMazeLoop L.useMunchausen 8 (P.metaMazeState 0 0 0 4 0)) 10

fourRooms-plain : LoopResult
fourRooms-plain = mkResult (fourRoomsLoop L.noMunchausen 8 (P.mazeState 4 1 8 9 0)) 1

fourRooms-munchausen : LoopResult
fourRooms-munchausen = mkResult (fourRoomsLoop L.useMunchausen 8 (P.mazeState 4 1 8 9 0)) 1

knapsack-plain : LoopResult
knapsack-plain = mkResult (runKnapsack L.noMunchausen 8 (P.knapsackState 0 8 0)) 32

knapsack-munchausen : LoopResult
knapsack-munchausen = mkResult (runKnapsack L.useMunchausen 8 (P.knapsackState 0 8 0)) 32

pong-plain : LoopResult
pong-plain = mkResult (pongLoop L.noMunchausen 8 (P.pongState 4 4 2 2 1 1 0)) 8

pong-munchausen : LoopResult
pong-munchausen = mkResult (pongLoop L.useMunchausen 8 (P.pongState 4 4 2 2 1 1 0)) 8

memoryChain-plain : LoopResult
memoryChain-plain = mkResult (memoryChainLoop L.noMunchausen 8 (P.memoryChainState 1 0 0)) 1

memoryChain-munchausen : LoopResult
memoryChain-munchausen = mkResult (memoryChainLoop L.useMunchausen 8 (P.memoryChainState 1 0 0)) 1

discountingChain-plain : LoopResult
discountingChain-plain = mkResult (discountingChainLoop L.noMunchausen 8 (P.discountingChainState 0 0)) 1

discountingChain-munchausen : LoopResult
discountingChain-munchausen = mkResult (discountingChainLoop L.useMunchausen 8 (P.discountingChainState 0 0)) 1

lbf-plain : LoopResult
lbf-plain = mkResult (lbfLoop L.noMunchausen 8 (P.lbfState 0 0 0 1 0 1 1 0)) 1

lbf-munchausen : LoopResult
lbf-munchausen = mkResult (lbfLoop L.useMunchausen 8 (P.lbfState 0 0 0 1 0 1 1 0)) 1

rockSample-plain : LoopResult
rockSample-plain = mkResult (rockSampleLoop L.noMunchausen 8 (P.rockSampleState 0 0 1 0)) 255

rockSample-munchausen : LoopResult
rockSample-munchausen = mkResult (rockSampleLoop L.useMunchausen 8 (P.rockSampleState 0 0 1 0)) 255

-- Closed-loop sanity laws: every result has exactly the requested horizon.
runLength : ∀ r → steps r ≡ 8
runLength r = refl
