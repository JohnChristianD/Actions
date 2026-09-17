# Full-coupled closed-loop benchmark results

These are deterministic results from the finite semantic mirror of `GeneralClosedLoopBenchV2.agda`, not an Agda executable run. The local environment has no Agda binary, and the GitHub Actions connector exposed no workflow run for the current branch head, so these values are not presented as typechecked execution output.

Both modes use the same initial state, horizon, action space, and environment transition function. The only changed learner field is `MunchausenMode`: `noMunchausen` versus the repository's finite negative-q shaping branch. This shaping is **not** a floating-point implementation of the canonical `alpha * log pi(a|s)` Munchausen formula; it is the monolithic finite `Int8` signal already defined in the learner.

| Environment | Horizon | Plain return | Plain regret | Plain success | Plain steps | Negative-q/Munchausen return | Negative-q/Munchausen regret | Negative-q/Munchausen success | Negative-q/Munchausen steps |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| knapsack | 16 | 16 | 0 | 1 | 6 | 16 | 0 | 1 | 6 |
| maze | 32 | 0 | 1 | 0 | 32 | 0 | 1 | 0 | 32 |
| metamaze | 32 | 0 | 10 | 0 | 32 | 0 | 10 | 0 | 32 |
| fourrooms | 32 | 0 | 1 | 0 | 32 | 0 | 1 | 0 | 32 |
| cartpole | 16 | 0 | 500 | 0 | 16 | 0 | 500 | 0 | 16 |
| BernoulliBandit | 16 | 11 | 79 | 0 | 16 | 14 | 76 | 0 | 16 |
| LBF | 16 | 1 | 0 | 0 | 16 | 0 | 1 | 0 | 16 |
| Pong | 16 | 16 | 0 | 0 | 16 | 16 | 0 | 0 | 16 |
| MemoryChain | 16 | 8 | 0 | 0 | 16 | 2 | 0 | 0 | 16 |
| DiscountingChain | 16 | 5 | 0 | 0 | 16 | 5 | 0 | 0 | 16 |
| RockSample | 16 | 0 | 255 | 0 | 16 | 0 | 255 | 0 | 16 |

The reward/regret numbers above are exact outputs of the deterministic mirror under the current finite ports. They are intentionally reported as raw benchmark facts rather than aggregated statistical analysis.

## Interpretation boundary

The benchmark is useful for checking the ceteris-paribus interface and for catching gross mode-dependent behavioral changes. It is **not** a claim that the finite port projections reproduce the full Gymnax environments. In particular, CartPole is currently a discrete quantized port rather than Gymnax's continuous dynamics, and the current default horizons are much shorter than several Gymnax report horizons.

Gymnax's current README reports checkpoint returns of 500 for CartPole-v1, 90 for BernoulliBandit-misc, 32 for MetaMaze-misc, 1 for FourRooms-misc, 0.1 for MemoryChain-bsuite, and 1.1 for DiscountingChain-bsuite. Those values are reference reports, not direct same-environment measurements of this finite benchmark.
