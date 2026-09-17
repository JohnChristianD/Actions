# General closed-loop benchmark results

Date: 2026-09-17

Active suite only. RockSample and Maze-v0 are absent by design. This sheet reports return, executed steps, and distinct actions. Terminal success is omitted as redundant with the finite termination convention used by each fixture.

The rows below are the exact deterministic replay values previously recorded for this same 12-environment active suite. They are replay evidence under the repository's finite semantics, not stochastic training statistics and not a substitute for Agda CI.

| Environment | Horizon | Arm | Return | Steps | Distinct actions |
|---|---:|---|---:|---:|---:|
| Jumanji Knapsack | 16 | no-Munchausen | 16 | 6 | 2 |
| Jumanji Knapsack | 16 | negative-Q-Munchausen | 16 | 7 | 2 |
| Gymnax MetaMaze | 32 | no-Munchausen | 0 | 32 | 4 |
| Gymnax MetaMaze | 32 | negative-Q-Munchausen | 0 | 32 | 4 |
| Gymnax FourRooms | 32 | no-Munchausen | 0 | 32 | 4 |
| Gymnax FourRooms | 32 | negative-Q-Munchausen | 0 | 32 | 4 |
| Gymnax CartPole-quantized | 16 | no-Munchausen | 0 | 16 | 2 |
| Gymnax CartPole-quantized | 16 | negative-Q-Munchausen | 0 | 16 | 2 |
| Gymnax BernoulliBandit | 16 | no-Munchausen | 12 | 16 | 2 |
| Gymnax BernoulliBandit | 16 | negative-Q-Munchausen | 2 | 16 | 2 |
| LevelBasedForaging | 16 | no-Munchausen | 0 | 16 | 6 |
| LevelBasedForaging | 16 | negative-Q-Munchausen | 0 | 16 | 6 |
| Gymnax Pong-misc | 16 | no-Munchausen | 16 | 16 | 3 |
| Gymnax Pong-misc | 16 | negative-Q-Munchausen | 16 | 16 | 3 |
| MemoryChain | 16 | no-Munchausen | 8 | 16 | 2 |
| MemoryChain | 16 | negative-Q-Munchausen | 10 | 16 | 2 |
| DiscountingChain | 16 | no-Munchausen | 1 | 16 | 5 |
| DiscountingChain | 16 | negative-Q-Munchausen | 1 | 16 | 5 |
| POBAX T-Maze | 8 | no-Munchausen | 0 | 2 | 1 |
| POBAX T-Maze | 8 | negative-Q-Munchausen | 0 | 2 | 1 |
| Uniform GaussianBandit slot | 16 | no-Munchausen | 1 | 16 | 2 |
| Uniform GaussianBandit slot | 16 | negative-Q-Munchausen | 8 | 16 | 2 |
| Jumanji/pgx 2048 projection | 32 | no-Munchausen | 222 | 32 | 4 |
| Jumanji/pgx 2048 projection | 32 | negative-Q-Munchausen | 269 | 32 | 4 |

New-port replay snapshots retained from the active suite:

- POBAX T-Maze: plain `Q=[0,0,0]`, counts `[1,0,0]`; negative-Q-Munchausen `Q=[239,0,0]`, counts `[1,0,0]`.
- Uniform GaussianBandit slot: plain `Q=[1,0]`, counts `[9,7]`; negative-Q-Munchausen `Q=[215,1]`, counts `[14,2]`.
- Jumanji/pgx 2048 projection: plain `Q=[16,22,24,160]`, counts `[3,4,4,21]`; negative-Q-Munchausen `Q=[7,2,242,2]`, counts `[10,8,8,6]`.

The active metric surface intentionally excludes regret. Historical signed-shortfall values are not current Agda `LoopResult` facts and are no longer presented as active benchmark metrics.

The negative-Q-Munchausen mode remains the canonical finite sign-flipped magnitude-coupled shaping mode. These finite values are not a claim of floating-point identity with the usual real-valued `alpha log pi` expression.
