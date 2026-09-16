{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalPolicyClosedLoopBench where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _∸_)
open import Data.Nat using (_<ᵇ_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)

open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalLearnerGameExecution_test
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P
open import Exotic.ERL.FullCoupled.GymnaxCartPoleClosedLoop_test
open import Exotic.ERL.FullCoupled.GymnaxCartPolePolicyClosedLoop_test

projectBinary4 : Fin 2 → Fin 4
projectBinary4 a with toℕ a
... | zero = fromℕ< (m%n<n 0 4)
... | _ = fromℕ< (m%n<n 1 4)

projectBinary5 : Fin 2 → Fin 5
projectBinary5 a with toℕ a
... | zero = fromℕ< (m%n<n 0 5)
... | _ = fromℕ< (m%n<n 1 5)

projectBinary6 : Fin 2 → Fin 6
projectBinary6 a with toℕ a
... | zero = fromℕ< (m%n<n 0 6)
... | _ = fromℕ< (m%n<n 1 6)

benchmark-policy-action : FullLearnerState → Fin 2
benchmark-policy-action s with policyChoosesLeft (canonicalPolicy learnerKernel s)
... | enabled = fromℕ< (m%n<n 0 2)
... | disabled = fromℕ< (m%n<n 1 2)

knapsackInitial : P.KnapsackState
knapsackInitial = P.knapsackState 0 3 0

knapsackOneStep : P.StepResult P.KnapsackState
knapsackOneStep = P.knapsackStep chooseItem1 knapsackInitial

knapsackClosedLoopLearner : FullLearnerState
knapsackClosedLoopLearner =
  closedLoopStep learnerKernel learnerInitial
    (fromℕ< (m%n<n 1 2))
    (P.reward knapsackOneStep)

knapsackMetrics : BenchMetrics P.KnapsackState
knapsackMetrics = benchMetrics
  (toℕ (P.code (P.reward knapsackOneStep)))
  6
  (6 ∸ toℕ (P.code (P.reward knapsackOneStep)))
  0
  1

knapsackMetrics-exact : knapsackMetrics ≡ benchMetrics 4 6 2 0 1
knapsackMetrics-exact = refl

mazeInitial : P.MazeState
mazeInitial = P.mazeState 0 0 0 1 0

mazeOneStep : P.StepResult P.MazeState
mazeOneStep = P.mazeStep (fromℕ< (m%n<n 1 4)) mazeInitial

mazeClosedLoopLearner : FullLearnerState
mazeClosedLoopLearner =
  closedLoopStep learnerKernel learnerInitial
    (projectBinary4 (benchmark-policy-action learnerInitial))
    (P.reward mazeOneStep)

mazeMetrics : BenchMetrics P.MazeState
mazeMetrics = benchMetrics
  (toℕ (P.code (P.reward mazeOneStep)))
  1
  (1 ∸ toℕ (P.code (P.reward mazeOneStep)))
  1
  1

mazeMetrics-exact : mazeMetrics ≡ benchMetrics 1 1 0 1 1
mazeMetrics-exact = refl

metaMazeInitial : P.MetaMazeState
metaMazeInitial = P.metaMazeState 0 0 0 1 0

metaMazeOneStep : P.StepResult P.MetaMazeState
metaMazeOneStep = P.metaMazeStep (fromℕ< (m%n<n 1 4)) metaMazeInitial

metaMazeMetrics : BenchMetrics P.MetaMazeState
metaMazeMetrics = benchMetrics
  (toℕ (P.code (P.reward metaMazeOneStep)))
  10
  (10 ∸ toℕ (P.code (P.reward metaMazeOneStep)))
  1
  1

metaMazeMetrics-exact : metaMazeMetrics ≡ benchMetrics 10 10 0 1 1
metaMazeMetrics-exact = refl

fourRoomsInitial : P.MazeState
fourRoomsInitial = P.mazeState 0 0 0 1 0

fourRoomsOneStep : P.StepResult P.MazeState
fourRoomsOneStep = P.fourRoomsStep (fromℕ< (m%n<n 1 4)) fourRoomsInitial

fourRoomsMetrics : BenchMetrics P.MazeState
fourRoomsMetrics = benchMetrics
  (toℕ (P.code (P.reward fourRoomsOneStep)))
  1
  (1 ∸ toℕ (P.code (P.reward fourRoomsOneStep)))
  1
  1

fourRoomsMetrics-exact : fourRoomsMetrics ≡ benchMetrics 1 1 0 1 1
fourRoomsMetrics-exact = refl

bernoulliBestRight : P.BernoulliBanditState
bernoulliBestRight = P.bernoulliBanditState 1 0 0 0

bernoulliOneStep : P.StepResult P.BernoulliBanditState
bernoulliOneStep =
  P.bernoulliBanditStep (fromℕ< (m%n<n 1 2)) bernoulliBestRight

bernoulliMetrics : BenchMetrics P.BernoulliBanditState
bernoulliMetrics = benchMetrics
  (toℕ (P.code (P.reward bernoulliOneStep)))
  1
  (1 ∸ toℕ (P.code (P.reward bernoulliOneStep)))
  1
  1

bernoulliMetrics-exact : bernoulliMetrics ≡ benchMetrics 1 1 0 1 1
bernoulliMetrics-exact = refl

cartPoleMetrics : BenchMetrics GymnaxCartPoleFiniteState
cartPoleMetrics = policyCartPole-metrics

cartPoleMetrics-exact : cartPoleMetrics ≡ benchMetrics 2 500 498 0 2
cartPoleMetrics-exact = policyCartPole-metrics-exact

-- The binary sparsemax+LCB head is native on two-action tasks. Four-, five-,
-- and six-action games are exercised through explicit deterministic binary
-- projections; they are closed-loop integration fixtures, not claims that the
-- current two-action head is a full native four-/five-/six-action policy.
