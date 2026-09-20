{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalLearnerGameExecution_test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_; _<_; _≤_; _<ᵇ_; z≤n; s≤s)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P

portReward : P.Int8 → Int8
portReward r = int8OfNat (toℕ (P.code r))

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

learnerRewardStep-reward-insensitive : ∀ s r₁ r₂ →
  learnerRewardStep s r₁ ≡ learnerRewardStep s r₂
learnerRewardStep-reward-insensitive s r₁ r₂ = refl

learnerRewardStep-clock : ∀ s r → clock (learnerRewardStep s r) ≡ suc (clock s)
learnerRewardStep-clock s r =
  trans (canonicalFullStep-clock learnerKernel (injectReward s r))
    (cong suc (sym (plus-zero (clock s))))

maxCriticValue : CriticState → Int8
maxCriticValue q with toℕ (code (qLeft q)) <ᵇ toℕ (code (qRight q))
... | true = qRight q
... | false = qLeft q

halfInt8 : Int8 → Int8
halfInt8 x = int8OfNat (halfNat (toℕ (code x)))

closedLoopTarget : CriticState → Int8 → Int8
closedLoopTarget q r = int8Add r (halfInt8 (maxCriticValue q))

closedLoopCriticUpdate : CriticState → Fin 2 → Int8 → CriticState
closedLoopCriticUpdate q a r with toℕ a
... | zero = criticState (closedLoopTarget q r) (qRight q)
... | _ = criticState (qLeft q) (closedLoopTarget q r)

encodeActionReward : Fin 2 → Int8 → Int8
encodeActionReward a r with toℕ a
... | zero = r
... | _ = int8OfNat (128 + toℕ (code r))

decodeReward : Int8 → Int8
decodeReward x with toℕ (code x) <ᵇ 128
... | true = x
... | false = int8OfNat (toℕ (code x) ∸ 128)

decodeAction : Int8 → Fin 2
decodeAction x with toℕ (code x) <ᵇ 128
... | true = fromℕ< (m%n<n 0 2)
... | false = fromℕ< (m%n<n 1 2)

closedLoopWatkinsKernel : WatkinsKernel
closedLoopWatkinsKernel = mkWatkinsKernel
  (λ q z → closedLoopCriticUpdate q (decodeAction z) (decodeReward z))
  (λ q z → disabled)
  (λ t g → g)

updateLCBCountByAction : Fin 2 → LCBCountState → LCBCountState
updateLCBCountByAction a (lcbCountState l r t) with toℕ a
... | zero = lcbCountState (suc l) r (suc t)
... | _ = lcbCountState l (suc r) (suc t)

closedLoopAttentionSignal : FullLearnerKernel → FullLearnerState → Int8 → Int8
closedLoopAttentionSignal K s r = int8Add (canonicalSignal K s) r

closedLoopWatkinsStep : FullLearnerState → Fin 2 → Int8 → WatkinsState
closedLoopWatkinsStep s a r =
  watkinsStep closedLoopWatkinsKernel
    (watkinsState (critic (watkins s)) (encodeActionReward a r) (trace (watkins s)))

closedLoopAttentionStep : FullLearnerKernel → FullLearnerState → Int8 → LearnedSparsemaxAttention
closedLoopAttentionStep K s r = attentionStep K (attention s) (closedLoopAttentionSignal K s r)

closedLoopGRUStep : FullLearnerKernel → FullLearnerState → Int8 → GRUState
closedLoopGRUStep K s r =
  let p = learnedSparsemaxAttentionWeights (attention s)
      w = walshHadamardApply (liftAttention p)
  in gruStep (gru s)
    (int8Add (closedLoopAttentionSignal K s r) (attentionToGRU K w))

closedLoopOptimizerStep : FullLearnerKernel → FullLearnerState → Int8 → F4IntUState
closedLoopOptimizerStep K s r =
  f4ThetaStep (optimizerKernel K) (optimizer s) (closedLoopAttentionSignal K s r)

closedLoopStep : FullLearnerKernel → FullLearnerState → Fin 2 → Int8 → FullLearnerState
closedLoopStep K s a r =
  fullLearnerState (suc (clock s))
  (closedLoopWatkinsStep s a r)
  (closedLoopAttentionStep K s r)
  (closedLoopGRUStep K s r)
  (closedLoopOptimizerStep K s r)
  (norm s)
  (updateLCBCountByAction a (lcbCounts s))
  (canonicalQLogControl K s)
  (canonicalQLogStep K s)

closedLoopStep-clock : ∀ K s a r → clock (closedLoopStep K s a r) ≡ suc (clock s)
closedLoopStep-clock K s a r = refl

closedLoopInput-roundtrip : ∀ a r →
  decodeAction (encodeActionReward a r) ≡ a
closedLoopInput-roundtrip a r with toℕ a
... | zero = refl
... | suc zero = refl

closedLoopReward-roundtrip : ∀ a r →
  decodeReward (encodeActionReward a r) ≡ r
closedLoopReward-roundtrip a r with toℕ a
... | zero = refl
... | suc zero = refl

closedLoopLeftRewardLearns :
  qLeft (critic (closedLoopStep learnerKernel learnerInitial
    (fromℕ< (m%n<n 0 2)) one8)) ≡ one8
closedLoopLeftRewardLearns = refl

closedLoopRightRewardLearns :
  qRight (critic (closedLoopStep learnerKernel learnerInitial
    (fromℕ< (m%n<n 1 2)) one8)) ≡ one8
closedLoopRightRewardLearns = refl

record BenchSpec (N : Nat) (S : Set) : Set₁ where
  constructor benchSpec
  field
    initial : S
    horizon : Nat
    referenceReturn : Nat
    step : Fin N → S → P.StepResult S
    choose : FullLearnerState → Fin N
    learnerAction : FullLearnerState → Fin 2
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
          (closedLoopStep learnerKernel l (learnerAction spec l) (portReward r))
          (total + toℕ (P.code r)) (suc steps)
    ...   | P.no = loop n
          (closedLoopStep learnerKernel l (learnerAction spec l) (portReward r))
          e' (total + toℕ (P.code r)) (suc steps)

record BenchMetrics (S : Set) : Set where
  constructor benchMetrics
  field metricReturn metricReference metricRegret metricSuccess metricSteps : Nat
open BenchMetrics public

metrics : ∀ {N S} → BenchSpec N S → FullLearnerState → BenchMetrics S
metrics spec l =
  let r = runBench spec l
  in benchMetrics
    (totalReturn r)
    (referenceReturn spec)
    (referenceReturn spec ∸ totalReturn r)
    (success spec (totalReturn r) (environment r))
    (steps r)

canonicalBit : FullLearnerKernel → FullLearnerState → Fin 2
canonicalBit K s with policyChoosesLeft (canonicalPolicy K s)
... | enabled = fromℕ< (m%n<n 0 2)
... | disabled = fromℕ< (m%n<n 1 2)

cycle2 : Nat → Nat
cycle2 zero = zero
cycle2 (suc zero) = suc zero
cycle2 (suc (suc n)) = cycle2 n

lift4 : FullLearnerState → Fin 4
lift4 s = fromℕ< (m%n<n ((cycle2 (clock s) * 2) + toℕ (canonicalBit learnerKernel s)) 4)

knapsackSuccess : Nat → P.KnapsackState → Nat
knapsackSuccess total e with P.natEq (P.value e) 16
... | P.yes = 1
... | P.no = 0

mazeSuccess : Nat → P.MazeState → Nat
mazeSuccess total e with P.natEq (P.row e) (P.goalRow e)
... | P.yes with P.natEq (P.col e) (P.goalCol e)
...   | P.yes = 1
...   | P.no = 0
... | P.no = 0

metaMazeSuccess : Nat → P.MetaMazeState → Nat
metaMazeSuccess total e with P.natEq (P.row e) (P.goalRow e)
... | P.yes with P.natEq (P.col e) (P.goalCol e)
...   | P.yes = 1
...   | P.no = 0
... | P.no = 0

banditSuccess : Nat → P.BernoulliBanditState → Nat
banditSuccess total e with P.natEq total 16
... | P.yes = 1
... | P.no = 0

knapsackSpec : BenchSpec 2 P.KnapsackState
knapsackSpec = benchSpec
  (P.knapsackState 0 8 0)
  8 16
  P.knapsackStep
  (λ s → canonicalBit learnerKernel s)
  (λ s → canonicalBit learnerKernel s)
  knapsackSuccess

mazeSpec : BenchSpec 4 P.MazeState
mazeSpec = benchSpec
  (P.mazeState 0 0 4 4 0)
  16 1
  P.mazeStep
  lift4
  (λ s → canonicalBit learnerKernel s)
  mazeSuccess

metaMazeSpec : BenchSpec 4 P.MetaMazeState
metaMazeSpec = benchSpec
  (P.metaMazeState 0 0 4 4 0)
  16 10
  P.metaMazeStep
  lift4
  (λ s → canonicalBit learnerKernel s)
  metaMazeSuccess

fourRoomsSpec : BenchSpec 4 P.MazeState
fourRoomsSpec = benchSpec
  (P.mazeState 4 1 8 9 0)
  16 1
  P.fourRoomsStep
  lift4
  (λ s → canonicalBit learnerKernel s)
  mazeSuccess

cartPoleSpec : BenchSpec 2 P.CartPoleQuantizedState
cartPoleSpec = benchSpec
  (P.cartPoleQuantizedState 1 0 0 0 0)
  16 0
  P.cartPoleQuantizedStep
  (λ s → canonicalBit learnerKernel s)
  (λ s → canonicalBit learnerKernel s)
  (λ total e → 1)

banditBest0Spec : BenchSpec 2 P.BernoulliBanditState
banditBest0Spec = benchSpec
  (P.bernoulliBanditState 0 0 0 0)
  16 16
  P.bernoulliBanditStep
  (λ s → canonicalBit learnerKernel s)
  (λ s → canonicalBit learnerKernel s)
  banditSuccess

banditBest1Spec : BenchSpec 2 P.BernoulliBanditState
banditBest1Spec = benchSpec
  (P.bernoulliBanditState 1 0 0 0)
  16 16
  P.bernoulliBanditStep
  (λ s → canonicalBit learnerKernel s)
  (λ s → canonicalBit learnerKernel s)
  banditSuccess

knapsackMetrics : BenchMetrics P.KnapsackState
knapsackMetrics = metrics knapsackSpec learnerInitial

mazeMetrics : BenchMetrics P.MazeState
mazeMetrics = metrics mazeSpec learnerInitial

metaMazeMetrics : BenchMetrics P.MetaMazeState
metaMazeMetrics = metrics metaMazeSpec learnerInitial

fourRoomsMetrics : BenchMetrics P.MazeState
fourRoomsMetrics = metrics fourRoomsSpec learnerInitial

cartPoleMetrics : BenchMetrics P.CartPoleQuantizedState
cartPoleMetrics = metrics cartPoleSpec learnerInitial

banditBest0Metrics : BenchMetrics P.BernoulliBanditState
banditBest0Metrics = metrics banditBest0Spec learnerInitial

banditBest1Metrics : BenchMetrics P.BernoulliBanditState
banditBest1Metrics = metrics banditBest1Spec learnerInitial

check-knapsack-closed-loop-steps : metricSteps knapsackMetrics ≡ 5
check-knapsack-closed-loop-steps = refl

check-cartpole-closed-loop-steps : metricSteps cartPoleMetrics ≡ 16
check-cartpole-closed-loop-steps = refl

check-bandit-best0-return : metricReturn banditBest0Metrics ≡ 0
check-bandit-best0-return = refl

check-bandit-best0-regret : metricRegret banditBest0Metrics ≡ 16
check-bandit-best0-regret = refl

check-bandit-best0-success : metricSuccess banditBest0Metrics ≡ 0
check-bandit-best0-success = refl

check-bandit-best1-return : metricReturn banditBest1Metrics ≡ 16
check-bandit-best1-return = refl

check-bandit-best1-regret : metricRegret banditBest1Metrics ≡ 0
check-bandit-best1-regret = refl

check-bandit-best1-success : metricSuccess banditBest1Metrics ≡ 1
check-bandit-best1-success = refl

check-knapsack-return : metricReturn knapsackMetrics ≡ 16
check-knapsack-return = refl

check-knapsack-regret : metricRegret knapsackMetrics ≡ 0
check-knapsack-regret = refl

check-knapsack-success : metricSuccess knapsackMetrics ≡ 1
check-knapsack-success = refl

check-maze-return : metricReturn mazeMetrics ≡ 0
check-maze-return = refl

check-maze-regret : metricRegret mazeMetrics ≡ 1
check-maze-regret = refl

check-maze-success : metricSuccess mazeMetrics ≡ 0
check-maze-success = refl

check-meta-maze-return : metricReturn metaMazeMetrics ≡ 0
check-meta-maze-return = refl

check-meta-maze-regret : metricRegret metaMazeMetrics ≡ 10
check-meta-maze-regret = refl

check-meta-maze-success : metricSuccess metaMazeMetrics ≡ 0
check-meta-maze-success = refl

check-four-rooms-return : metricReturn fourRoomsMetrics ≡ 0
check-four-rooms-return = refl

check-four-rooms-regret : metricRegret fourRoomsMetrics ≡ 1
check-four-rooms-regret = refl

check-four-rooms-success : metricSuccess fourRoomsMetrics ≡ 0
check-four-rooms-success = refl

check-cartpole-return : metricReturn cartPoleMetrics ≡ 0
check-cartpole-return = refl

check-cartpole-regret : metricRegret cartPoleMetrics ≡ 0
check-cartpole-regret = refl
