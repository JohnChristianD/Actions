# General Closed-Loop Bench Results

Date: 2026-09-17
Branch: `main`

These are exact deterministic replays of the repository's finite benchmark semantics, not a statistical study and not a substitute for Agda typechecking. The two arms use the same initial state, action space, horizon, and environment transition; only `noMunchausen` versus the repository's finite negative-Q-Munchausen mode changes.

Metrics recorded by the bench are return, regret (`referenceReturn - return`), terminal success, executed steps, distinct actions, final Q table, and final action counts.

| Environment | Horizon | Arm | Return | Regret | Success | Steps | Distinct |
|---|---:|---|---:|---:|---:|---:|---:|
| Knapsack | 16 | no-Munchausen | 16 | 0 | 1 | 6 | 2 |
| Knapsack | 16 | negative-Q-Munchausen | 16 | 0 | 1 | 7 | 2 |
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
| POBAX T-Maze | 8 | no-Munchausen | 0 | 1 | 1 | 2 | 1 |
| POBAX T-Maze | 8 | negative-Q-Munchausen | 0 | 1 | 1 | 2 | 1 |
| Uniform GaussianBandit slot | 16 | no-Munchausen | 1 | 15 | 0 | 16 | 2 |
| Uniform GaussianBandit slot | 16 | negative-Q-Munchausen | 8 | 8 | 0 | 16 | 2 |
| Jumanji/pgx 2048 projection | 32 | no-Munchausen | 222 | -190 | 0 | 32 | 4 |
| Jumanji/pgx 2048 projection | 32 | negative-Q-Munchausen | 269 | -237 | 0 | 32 | 4 |

Exact new-port replay snapshots:

- POBAX T-Maze: plain `Q=[0,0,0]`, counts `[1,0,0]`; negative-Q-Munchausen `Q=[239,0,0]`, counts `[1,0,0]`.
- Uniform GaussianBandit slot: plain `Q=[1,0]`, counts `[9,7]`; negative-Q-Munchausen `Q=[215,1]`, counts `[14,2]`.
- Jumanji/pgx 2048 projection: plain `Q=[16,22,24,160]`, counts `[3,4,4,21]`; negative-Q-Munchausen `Q=[7,2,242,2]`, counts `[10,8,8,6]`.

RockSample and the Jumanji Maze-v0 path are permanently excluded from this closed-loop suite.

The negative-Q-Munchausen mode remains the canonical finite sign-flipped scale in this repository. These finite values are not a claim of floating-point identity with the usual `alpha log pi` formulation.

Gymnax reference points are external comparators only. The current Gymnax README reports checkpoint returns of CartPole-v1 500, BernoulliBandit-misc 90, MetaMaze-misc 32, FourRooms-misc 1, MemoryChain-bsuite 0.1, DiscountingChain-bsuite 1.1, and GaussianBandit-misc 0; it does not report a Pong checkpoint return in that table. These references are not numerically interchangeable with the finite projections above.

Agda verification status is separate. There is no local Agda executable in this execution environment, and no connected GitHub Actions run has been observed for these direct commits. The numbers above are therefore replay evidence for the declared finite semantics, not compiled-proof evidence.