# Canonical general-action closed-loop benchmark

## Canonical learner

`Exotic/ERL/FullCoupled/CanonicalGeneralLearnerMonolith.agda` is a self-contained learner file. It contains no environment imports. It includes finite Int8 arithmetic, finite rational/Mobius carrier, GRU hard-sign gate, recurrent x/(1-x)-style finite rational boundary, GRU quotient persistence, associative transition composition, arbitrary finite-action Q/count vectors, LCB scoring, sparsemax-induced action selection, learned attention, F4/L2 state, NormPair state, finite negative-Munchausen shaping, and the natural-number progress/finite-cycle contradiction.

The default action arity is 64.

## Why the binary bottleneck is removed

The previous closed-loop surface exposed `binaryAction : FullLearnerState -> Fin 2` and lifted it into larger environment alphabets. That was an adapter, not a true general-action learner.

The canonical general learner uses:

```text
QVec A      = Fin A -> Int8
CountVec A  = Fin A -> Nat
policyA     : GeneralLearnerState A -> Fin A
```

with LCB included in the action score. `sparsemaxDecisionA` returns the action selected by the sparsemax decision rule through the exact argmax property of sparsemax. The closed-loop environment receives that `Fin A` action directly; no binary projection is involved.

The module intentionally proves the decision-level theorem, not a claim that the stored Int8 action weights are a full exact real-valued sparsemax probability vector for arbitrary A. Exact general-A probability weights require a richer rational/vector construction; the action interface only needs the maximizer.

## Closed loop

`CanonicalGeneralClosedLoopBench.agda` threads the real learner state and environment state:

```text
learner_t
  -> policyA
  -> Fin A environment action
  -> environment step
  -> reward, environment_{t+1}
  -> generalLearnerStep
  -> learner_{t+1}
```

The learner is not reinitialized at each step.

Every benchmark record contains:

- `return`
- `regret = referenceReturn - return`, truncated in `Nat`
- `success`
- `steps`

Each game has paired `plain` and `munchausen` runs under the same initial state and horizon. The benchmark source records the two raw outcomes. No statistical analysis is performed in Agda.

## External baseline comparison

CleanRL's current public repository documents DQN on `CartPole-v1` and provides learning curves and a benchmark script using multiple seeds. Its DQN implementation is a replay-buffer + target-network algorithm, so its reported results are not an apples-to-apples comparison with this deterministic finite learner. See the CleanRL DQN docs and benchmark script.

Gymnax's current README reports accelerated environment reference results. The table includes CartPole-v1 PPO/ES return 500, FourRooms-misc PPO/ES return 1, MemoryChain-bsuite PPO/ES return 0.1, and DiscountingChain-bsuite PPO/ES return 1.1. Those are external reference results, not results of this learner, and they use different environment dynamics and algorithms.

Jumanji's current Knapsack implementation uses a random generator by default with 50 items and a total budget of 12.5, and accepts one item index per action. The repository's finite Agda port is therefore a deterministic finite benchmark projection, not an executable clone of JAX floating-point random generation. The distinction is intentional and must remain explicit.

## CNN theorem boundary

`CNNTransitionBisimulation.agda` now contains two levels:

1. `TransitionWitness`: decode, CNN transition, learner transition, and a commuting square.
2. `CNNKernelBisimulation`: an explicit state relation closed under the CNN transition and mapped into learner-visible equality.

The practical benefit is exact state deduplication. Once two CNN states are related, they can be represented by one cache representative without changing any future decoded learner state under any finite number of recurrent transitions covered by the theorem.

This is not a theorem that an arbitrary implementation is a CNN. A formal CNN definition still requires an explicit spatial state, local weight-sharing operator, receptive-field map, stride/padding convention, and composition structure. Those are outside the current finite learner signature.

## CI evidence

The branch updates `.github/workflows/agda.yml` so Agda checks both the canonical general-action learner and the general closed-loop benchmark. The current ChatGPT GitHub integration cannot create a pull request or dispatch a branch workflow, and the local execution environment has no Agda binary. Therefore the exact numeric benchmark normal forms are pending the repository's Agda CI gate rather than reported as already executed.
