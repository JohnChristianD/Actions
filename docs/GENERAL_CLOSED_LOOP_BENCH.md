# General finite-action learner benchmark

Default action arity: 64.

The learner monolith is `Exotic/ERL/FullCoupled/GeneralActionLearnerMonolith.agda`. Games remain separate in `Exotic/ERL/FullCoupled/CanonicalGamePorts.agda`; the benchmark adapter is `Exotic/ERL/FullCoupled/GeneralClosedLoopBench.agda`.

## Closed-loop semantics

Each step is threaded as

```text
learner state
  -> generalPolicy
  -> finite action
  -> game step
  -> reward + next game state
  -> generalStep
  -> next learner state
```

The learner is not reinitialized between environment steps. `generalStep-clock` and `generalNoFixedPoint` are checked on the learner transition.

## Action arity

The old canonical learner exposes an exact two-action sparsemax surface. The generalized monolith removes that architectural bottleneck at the interface level: `QVec A = Fin A -> Int8`, `CountVec A = Fin A -> Nat`, and the policy consumes arbitrary positive finite action arity.

The generalized selector is explicitly named `sparsemaxExtremeA`: it returns a simplex vertex with one-hot Int8 weight 128. This is an extreme-point sparse policy, not a claim that the finite Int8 implementation is the full Euclidean sparsemax projection for arbitrary A. The old exact two-action sparsemax equations remain separately checked.

## Munchausen ceteris paribus

Every game has two symbolic benchmark records:

- `*-plain` uses `noMunchausen`.
- `*-munchausen` uses `useMunchausen`.

Everything else in the generalized kernel is unchanged. The current finite kernel's Munchausen term is the repository's negative finite Int8 shaping term, `int8Neg reward`; it is not asserted here as a floating-point log-policy implementation.

## Metrics

`LoopResult` records:

- `return`: accumulated finite reward code.
- `regret`: `optimalReturn - return`, truncated at zero in `Nat`.
- `success`: 1 when a terminal success transition is observed, else 0.
- `steps`: actual closed-loop transitions executed.

These are raw finite benchmark values. No statistical aggregation, significance testing, or external data analysis is part of the Agda source.

## External references

CleanRL documents classic-control DQN separately from its Atari DQN. Its `dqn.py` supports CartPole-v1 with a discrete action network and uses replay/target-network DQN machinery. The maintained documentation exposes CartPole learning curves and benchmark scripts, but those experiments are not directly comparable to this deterministic finite Agda projection without matching environment dynamics, network, horizon, optimizer, exploration, and seeds.

Gymnax reports accelerated environment baselines in its README and `gymnax-blines`. The README lists, among others, CartPole-v1 PPO/ES with reported return 500, FourRooms-misc PPO/ES with return 1, MemoryChain-bsuite PPO/ES with return 0.1, and DiscountingChain-bsuite PPO/ES with return 1.1. Those are external reference reports, not measurements of this Agda learner.

## Evidence status

The source changes in this branch have been wired into `.github/workflows/agda.yml`, but the current ChatGPT execution environment does not contain an Agda executable and the GitHub connector cannot create a pull request or dispatch a workflow run from this branch. Consequently the exact numeric normalization of the benchmark records has not been externally observed here. The source is treated as pending CI verification rather than silently promoted to a completed benchmark.
