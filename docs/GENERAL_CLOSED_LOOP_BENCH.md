# General closed-loop learner bench

## Monolith boundary

`Exotic/ERL/FullCoupled/GeneralFullCoupledLearnerMonolith.agda` is the single self-contained learner component. It contains the finite action abstraction, Int8 finite arithmetic, score ordering, threshold-style sparsemax weights, Q/count state, Mobius trace, GRU state and transition, F4-style quantizer, norm state, and canonical finite negative-Q-Munchausen mode. It contains no theorem layer.

The theorem layer is `GeneralFullCoupledTheoremsMonolith.agda`, whose only learner dependency is the learner monolith.

## Sparsemax status

The old hard-coded 2-action boundary is removed. The learner accepts arbitrary finite `ActionSpace A`, with checked inhabitants for `A = 2`, `4`, and default width `64`.

The learner exposes the exact finite threshold numerator/denominator representation and a largest-valid-support scan. The theorem monolith records the KKT boundary and its simplex/denominator laws.

The full arbitrary-A real-valued Euclidean sparsemax projection theorem is **not** claimed complete by this commit. The remaining proof obligation is the bridge from the finite Int8 scan to the KKT support inequalities, stationarity, complementarity, and simplex normalization. It is kept explicit rather than hidden behind a theorem-shaped record with no algorithm-to-KKT derivation.

No `Data.List.Sort.MergeSort.Properties`, `Data.List.Relation.Unary.Sorted.TotalOrder.Properties`, or `Relation.Binary.Properties.DecTotalOrder` bundle is required by the current monolith. The learner owns its finite insertion sort; importing one of those proof stacks without replacing that implementation would increase dependency surface. For this exact architecture, `Data.Nat.Properties` is more relevant than an additional list-sort bundle once the arithmetic KKT bridge is discharged.

## Mobius/GRU semidirect coupling

`MobiusTrace = Nat -> MobiusAction` gives a depth-indexed action rather than a single fixed Mobius map. The theorem monolith proves prefix-action recursion, semidirect one-step factorization, direct coupling to the iterated GRU transition, and the depth-invariant persistent token tuple `(matrixZ, matrixR, matrixH, optimizerToken)`.

The remaining strengthening target is the fully indexed semidirect-product theorem over arbitrary traces, stated directly as an equality between prefix composition and the corresponding iterated GRU transition rather than as two independent algebraic lemmas.

## External CNN theorem boundary

The theorem monolith uses an abstract finite-depth machine with an encoder, local step, translation action, equivariance law, representation adapter, and downstream transition. The proof establishes representation-equality preservation through the downstream transition and lifts it to the finite-depth comparison class.

No concrete convolution kernel, tensor layout, padding rule, stride, learned parameter tensor, or trained CNN is embedded into learner semantics. This matches the standard formalization boundary where a CNN is treated as a modular finite-depth mathematical machine rather than smuggled into the RL state definition. SciSpace-indexed formal work by Vertechi and Bergomi gives a modular finite-depth neural-network construction covering convolutional and recurrent architectures, while Zhao et al. give a hierarchical formal CNN verification framework. The repository theorem stays at the abstract interface boundary.

## Closed-loop bench

`GeneralClosedLoopBenchV2.agda` executes:

`learner state -> policy -> finite action -> environment step -> reward/next state -> learner step`.

The exact `LoopResult` records return, regret, terminal success, actual steps, and distinct actions. `AblationPair` holds the environment and horizon fixed while changing only `noMunchausen` versus `munchausen`.

The active suite contains CartPole-quantized, BernoulliBandit, MetaMaze, FourRooms, Jumanji Knapsack, LevelBasedForaging, Pong, MemoryChain, DiscountingChain, POBAX T-Maze, a deterministic Uniform replacement in the Gymnax GaussianBandit-misc slot, and a finite Jumanji/pgx 2048 projection.

RockSample and Maze-v0 are permanently excluded.

## Benchmark evidence

`docs/GENERAL_CLOSED_LOOP_BENCH_RESULTS_20260917.md` contains exact deterministic replay returns, regrets, success flags, step counts, distinct-action counts, and Q/count snapshots for the active suite. These are finite replay results, not statistical aggregation and not Agda proof evidence.

The negative-Q-Munchausen signal remains the repository's canonical finite sign-flipped magnitude-coupled shaping mode. It is deliberately not relabeled as the floating-point `alpha log pi` formula.

Gymnax is used only as an external reference family. Its current README reports checkpoint returns including CartPole-v1 `500`, BernoulliBandit-misc `90`, MetaMaze-misc `32`, FourRooms-misc `1`, MemoryChain-bsuite `0.1`, DiscountingChain-bsuite `1.1`, and GaussianBandit-misc `0`. The repository's finite projections are not directly numerically interchangeable with those reference environments.

## Verification

The GitHub Actions workflow now explicitly checks the generalized learner monolith, theorem monolith, closed-loop bench, and additional benchmark ports before the legacy gates. No local Agda executable is available in the current execution environment, so these direct commits should not be described as compiler-verified until an external workflow run is observed.