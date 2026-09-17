# General Closed-Loop Bench Results

Date: 2026-09-17
Branch: `general-fininteger-policy-closedloop-20260916`

These are deterministic replay results from the current `GeneralClosedLoopBenchV2.agda` semantics. They are a reference-interpreter replay of the Agda definitions, not an Agda compiler/CI execution. No stochastic aggregation is used.

The two arms are ceteris-paribus: the same initial state, action space, horizon, and environment transition are used. The only learner-mode change is `noMunchausen` versus the repository's finite `negativeMunchausen` signal.

Metrics are exact: return, regret (`referenceReturn - return`), terminal success, executed steps, distinct actions, final Q table, and final action counts.

| Environment | Horizon | Arm | Return | Regret | Success | Steps | Distinct actions |
|---|---:|---|---:|---:|---:|---:|---:|
| Knapsack | 16 | no-Munchausen | 16 | 0 | 1 | 6 | 2 |
| Knapsack | 16 | negative-Q-Munchausen | 16 | 0 | 1 | 7 | 2 |
| Maze | 32 | no-Munchausen | 0 | 1 | 0 | 32 | 4 |
| Maze | 32 | negative-Q-Munchausen | 0 | 1 | 0 | 32 | 4 |
| MetaMaze | 32 | no-Munchausen | 0 | 10 | 0 | 32 | 4 |
| MetaMaze | 32 | negative-Q-Munchausen | 0 | 10 | 0 | 32 | 4 |
| FourRooms | 32 | no-Munchausen | 0 | 1 | 0 | 32 | 4 |
| FourRooms | 32 | negative-Q-Munchausen | 0 | 1 | 0 | 32 | 4 |
| CartPole-quantized | 16 | no-Munchausen | 0 | 500 | 0 | 16 | 2 |
| CartPole-quantized | 16 | negative-Q-Munchausen | 0 | 500 | 0 | 16 | 2 |
| BernoulliBandit | 16 | no-Munchausen | 12 | 78 | 0 | 16 | 2 |
| BernoulliBandit | 16 | negative-Q-Munchausen | 2 | 88 | 0 | 16 | 2 |
| LBF | 16 | no-Munchausen | 0 | 1 | 0 | 16 | 6 |
| LBF | 16 | negative-Q-Munchausen | 0 | 1 | 0 | 16 | 6 |
| Pong | 16 | no-Munchausen | 16 | -8 | 0 | 16 | 3 |
| Pong | 16 | negative-Q-Munchausen | 16 | -8 | 0 | 16 | 3 |
| MemoryChain | 16 | no-Munchausen | 8 | -7 | 0 | 16 | 2 |
| MemoryChain | 16 | negative-Q-Munchausen | 10 | -9 | 0 | 16 | 2 |
| DiscountingChain | 16 | no-Munchausen | 1 | 0 | 0 | 16 | 5 |
| DiscountingChain | 16 | negative-Q-Munchausen | 1 | 0 | 0 | 16 | 5 |
| RockSample | 16 | no-Munchausen | 0 | 255 | 0 | 16 | 6 |
| RockSample | 16 | negative-Q-Munchausen | 0 | 255 | 0 | 16 | 6 |

Final Q/count snapshots from the same replay:

- Knapsack: plain `Q=[4,12], counts=[2,3]`; negative-Q-Munchausen `Q=[221,8], counts=[4,2]`.
- Maze/MetaMaze/FourRooms: plain `Q=[0,0,0,0], counts=[11,7,7,7]`; negative-Q-Munchausen `Q=[222,239,239,0], counts=[28,1,1,2]`.
- CartPole: plain `Q=[0,0], counts=[9,7]`; negative-Q-Munchausen `Q=[207,0], counts=[14,2]`.
- BernoulliBandit: plain `Q=[12,0], counts=[12,4]`; negative-Q-Munchausen `Q=[241,224], counts=[2,14]`.
- LBF: plain `Q=[0,0,0,0,0,0], counts=[3,3,3,3,2,2]`; negative-Q-Munchausen `Q=[222,239,239,239,239,0], counts=[10,1,1,1,1,2]`.
- Pong: plain `Q=[6,5,5], counts=[6,5,5]`; negative-Q-Munchausen `Q=[235,240,2], counts=[13,1,2]`.
- MemoryChain: plain `Q=[8,0], counts=[11,5]`; negative-Q-Munchausen `Q=[217,0], counts=[14,2]`.
- DiscountingChain: plain `Q=[1,0,0,0,0], counts=[4,3,3,3,3]`; negative-Q-Munchausen `Q=[220,239,239,239,0], counts=[11,1,1,1,2]`.
- RockSample: plain `Q=[0,0,0,0,0,0], counts=[3,3,3,3,2,2]`; negative-Q-Munchausen `Q=[222,239,239,239,239,0], counts=[10,1,1,1,1,2]`.

Interpretation is deliberately descriptive rather than statistical: the finite negative-Q shaping signal is active and materially changes Q/count trajectories on several environments. This does not establish a general performance claim because the suite is deterministic, horizons are intentionally short, and several ports are simplified finite projections rather than faithful Gymnax implementations.

Agda verification status remains separate: the repository has no locally installed Agda executable in this environment, and no GitHub Actions run was observable for the branch at the time this report was written.
