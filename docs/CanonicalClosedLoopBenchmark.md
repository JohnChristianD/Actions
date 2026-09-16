# Canonical closed-loop benchmark

Default learner width is `d = 64` at the replication interface. The current core GRU record remains the scalar finite carrier; `d=64` is the declared representation/default width, not a retroactive claim that the scalar `GRUState` is already a `Fin 64 -> Int8` vector.

## Execution contract

Each benchmark is a pure closed loop:

```text
learner state
  -> canonical sparsemax + LCB action bit
  -> deterministic action-space lift when the environment has >2 actions
  -> environment step
  -> raw environment reward
  -> finite negative-Munchausen reward shaping
  -> learner update
  -> next learner state
```

Raw return is accumulated from the environment reward only. The shaped reward is used inside the learner update and is never substituted for reported environment return.

`CanonicalClosedLoopLearner.agda` provides the reward-conditioned learner transition. `CanonicalEndToEndFaithfulBench2.agda` provides the modular environment interface. `CanonicalEndToEndFaithfulBench_test.agda` asserts exact reductions.

## Exact deterministic benchmark snapshot

These values are the reduction targets asserted by the Agda test surface. `regret` is the finite reference gap `referenceReturn - return`, clamped at zero by Nat subtraction. It is not a stochastic estimator.

| Environment | horizon | return | reference | regret | success |
| --- | ---: | ---: | ---: | ---: | ---: |
| CartPole finite projection | 16 | 0 | 500 | 500 | 1 |
| Bernoulli bandit, best action 0 | 16 | 14 | 16 | 2 | 0 |
| Bernoulli bandit, best action 1 | 16 | 14 | 16 | 2 | 0 |
| Jumanji Knapsack fixed finite instance | 8 | 4 | 6 | 2 | 0 |
| Jumanji Maze-v0 fixed ToyGenerator map | 16 | 0 | 1 | 1 | 0 |
| Gymnax MetaMaze finite projection | 16 | 0 | 10 | 10 | 0 |
| Gymnax FourRooms fixed map | 16 | 0 | 1 | 1 | 0 |
| Jumanji LevelBasedForaging finite projection | 16 | 0 | 1 | 1 | 0 |
| Gymnax Pong-misc finite projection | 16 | 16 | 16 | 0 | 1 |
| Gymnax MemoryChain-bsuite fixed context/query | 6 | 1 | 1 | 0 | 1 |
| Gymnax DiscountingChain-bsuite, returns scaled x10 | 4 | 10 | 11 | 1 | 1 |
| Pobax RockSample finite projection | 16 | 0 | 1 | 1 | 0 |

The benchmark is intentionally deterministic. MemoryChain fixes the sampled context/query, and DiscountingChain fixes the mapping seed. Jumanji Knapsack uses a fixed two-item instance that preserves the upstream valid/invalid-action and dense-reward semantics. These choices remove statistical assumptions from the formal test.

## Published reference points

Gymnax's current README reports checkpoint returns including CartPole-v1 `R: 500`, FourRooms-misc `R: 1`, MemoryChain-bsuite `R: 0.1`, and DiscountingChain-bsuite `R: 1.1`. Gymnax also provides PPO/ES checkpoints for MetaMaze-misc and other tasks. See https://github.com/RobertTLange/gymnax .

CleanRL describes its implementations as single-file, research-friendly implementations and maintains benchmark scripts/results across many algorithms and games. Its repository has a CartPole-v1 DQN checkpoint/evaluation path, but this repository does not expose a directly comparable deterministic return table for the exact finite projections above. See https://github.com/vwxyzjn/cleanrl .

The comparison is therefore semantic rather than a leaderboard claim:

- Gymnax reference numbers are measurements of its actual JAX environments and trained PPO/ES agents, not these finite Agda projections.
- CleanRL reference numbers are measurements of its own Gymnasium implementations and training procedures, not these finite Agda projections.
- No claim of performance parity is made.

## Negative-Munchausen algebra

The maintained formal name is `negativeMunchausenReward8`. Its structure is the standard Munchausen reward-shaping pattern with the coefficient sign flipped:

```text
base reward + (-alpha) * finiteMaxEntQLog8(policy weight)
```

The current finite max-entropy carrier is `finiteMaxEntQLog8 = finiteQLog8`. The formal development uses finite rational encoding rather than a real transcendental logarithm. It proves:

- the negative scale is the involutive sign flip of the positive scale;
- the positive and negative scale codes cancel in the Int8 carrier;
- the negative bonus is exactly the positive bonus with the scale sign flipped;
- the finite max-entropy q-log carrier is the existing endogenous finite q-log object.

This is algebraically aligned with Munchausen RL and q-Munchausen RL, not a claim that the finite carrier implements real-valued logarithms exactly. The q-Munchausen literature explicitly motivates q-logarithms when using Tsallis/sparsemax-style maximum-entropy policies because the ordinary logarithm is mismatched with that entropy family.

## Minimal CNN composition

The useful theorem is no longer "CNNs are equivalent" in the vague architectural sense. The exact interface is only:

```text
CNNLogPyramidCode
      |
      | cnnToAttention
      v
LearnedSparsemaxAttention
      |
      | replaceAttention
      v
FullLearnerState
      |
      | canonicalFullStep
      v
FullLearnerState
```

The theorem says:

```text
cnnToAttention p == cnnToAttention q
------------------------------------
cnn trajectory from p == cnn trajectory from q
```

for every finite number of recurrent steps.

Practically, this means two encoders can be swapped without changing the learner trajectory whenever they emit the same decoder-level attention state. The theorem is exact and does not require a metric, approximation bound, CNN function-class comparison, or claim that one architecture is more expressive than another.

The next stronger step, if ever needed, is a genuine encoder/decoder bisimulation with an explicit encoder state, inverse/reconstruction law, and a metric for approximate equivalence. None of those are asserted by the current benchmark.
