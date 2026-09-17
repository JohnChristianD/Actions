# General closed-loop learner bench

## Canonical boundary

`Exotic/ERL/FullCoupled/GeneralFullCoupledLearnerMonolith.agda` is the single self-contained learner monolith. It is environment-agnostic and uses the finite-action surfaces `QVec A = Fin A -> Int8` and `CountVec A = Fin A -> Nat`.

The learner's direct imports are kept to the finite arithmetic core: `Agda.Builtin.Nat`, `Data.Nat`, `Data.Fin`, `Data.Fin.Properties`, `Data.Nat.DivMod`, and `Data.Product`.

Default width is `d = 64`, and `powerOfFour64` constructs the witness `64 = 4^3` in the proof layer.

## Sparsemax action arity and proof boundary

The old 2-action interface is no longer the type boundary. `actionSpace2`, `actionSpace4`, and `defaultActionSpace : ActionSpace 64` are all instances of the same `ActionSpace A` interface.

The kernel performs finite score ordering and now keeps the largest valid finite support found by the support scan. `SparseWeight` exposes the threshold-style numerator/denominator representation.

This is still **not** the full arbitrary-A Euclidean sparsemax KKT/simplex theorem. The theorem monolith now contains an explicit `SparsemaxKKTData` certificate and exact simplex/denominator laws, but the algorithm-to-certificate bridge is deliberately still absent. In particular, no theorem is claiming that the current modular `Int8` scorer, support predicate, and finite scan already establish the real-valued sparsemax KKT stationarity/complementarity equations. No postulate or theorem shell is being used to conceal that gap.

`Data.List.Sort.MergeSort.Properties` is not imported merely as decoration. The current learner owns a custom self-contained list and insertion sort; importing the stdlib merge-sort proof bundle without replacing that implementation would add dependency surface without proving the missing KKT bridge. The stdlib module itself packages permutation and sortedness correctness for its own `List`/order stack.

## Closed-loop semantics

The intended loop is:

`learner state -> generalPolicy -> finite action -> modular game step -> reward/next game state -> learnerStep -> next learner state`.

`GeneralClosedLoopBenchV2.agda` implements that learner-selected loop and records exact finite values:

- `return`: cumulative encoded reward,
- `regret`: `referenceReturn - return` under Nat subtraction,
- `success`: terminal-success bit,
- `steps`: actual transitions executed.

The ordinary `AblationPair` keeps the environment, horizon, initial state, action space, optimizer, GRU, NormPair, and reward adapter fixed while changing only `MunchausenMode`.

`NegativeQMunchausenBench.agda` adds the requested ceteris-paribus **negative-Q-Munchausen vs no-Q-Munchausen** path. The repository's finite negative-Q scale remains explicitly sign-flipped and magnitude-coupled to the finite Q representation; this is intentionally canonical for this finite model, not a claim of numerical identity with floating-point `alpha * log pi` Munchausen shaping.

## Trace-valued Mobius/GRU coupling

`GeneralFullCoupledLearnerMonolith.agda` contains the semantic trace representation `MobiusTrace : Nat -> MobiusAction`, `prefixAction`, and the semidirect transition surface. The proofs now live in `GeneralFullCoupledTheoremsMonolith.agda` and connect prefix composition directly to iterated `gruStep`, including the depth-lifted persistent-token invariant.

This is the missing algebraic link that was absent when Mobius composition and GRU persistence were treated as independent facts.

## Environment suite

The current closed-loop suite keeps CartPole, BernoulliBandit, MetaMaze, FourRooms, Jumanji Knapsack, LevelBasedForaging, Pong, MemoryChain, DiscountingChain, and POBAX T-Maze.

RockSample and the Jumanji Maze-v0 path are intentionally and permanently excluded from the new bench.

`AdditionalBenchmarkPorts.agda` adds the requested deterministic **Uniform** finite projection for the Gymnax GaussianBandit-misc slot and a finite 2048 projection carrying both Jumanji and pgx provenance names. Gaussian reward arithmetic is intentionally replaced by a uniform finite reward cycle, rather than importing Gaussian arithmetic or randomness into the learner.

The 2048 port is a formal finite projection of the Jumanji/pgx action contract, not a claim that the monolith contains a complete 4x4 engine.

## Gymnax published reference points

Gymnax's current README lists checkpoint returns of:

- CartPole-v1: `500`
- BernoulliBandit-misc: `90`
- MetaMaze-misc: `32`
- FourRooms-misc: `1`
- MemoryChain-bsuite: `0.1`
- DiscountingChain-bsuite: `1.1`
- GaussianBandit-misc: `0`

The same table lists Pong-misc without a checkpoint return. Gymnax says its displayed throughput figures are estimated for 1M random-policy transitions on an NVIDIA A100 using JIT-compiled episode rollouts with 2000 workers. Those figures are not used as claims about this Agda learner.

Gymnax's functional interface is structurally comparable: policy action selection, `env.step`, reward/next-state propagation, and scan-style rollout execution.

## Benchmark result status

The source records the exact result objects, including regret, success, and steps, and the ceteris-paribus Munchausen/negative-Q-Munchausen ablations are present. What is missing is an executed observer: this execution environment has no local Agda executable, and the latest development-branch commit has returned **no GitHub Actions workflow run or commit status** through the connected GitHub interface. Therefore there are **no verified observed return/regret/success/steps numbers** to report yet.

The authoritative outputs to record after an external Agda run are the concrete `LoopResult` values from `GeneralClosedLoopBenchV2` and the concrete `QMunchausenAblation` values from `NegativeQMunchausenBench`. I am not inventing Pong or any other return as evidence of CNN replacement.

## Theorem monolith

`GeneralFullCoupledTheoremsMonolith.agda` is now the single theorem layer depending only on the learner monolith for this generalized path. It contains the clock/non-fixed-point family, GRU persistence/equivalence, trace-valued Mobius semidirect laws, the explicit sparsemax KKT data boundary, and the external CNN comparison class.

The CNN side remains learner-agnostic. The theorem layer models only an abstract finite-depth/local representation stack, translation/equivariance obligations, a representation adapter, and downstream transition preservation. No concrete CNN kernel, stride, padding rule, tensor layout, trained weight, or CNN implementation is smuggled into learner semantics.

## Evidence status

No local Agda compiler is present in this execution environment. The branch workflow is configured to typecheck the two monoliths and the benchmark ports, but the current connected GitHub view has not exposed a run/status for the latest direct commits. Until that external proof run exists, the repository should treat theorem compilation and benchmark numbers as pending verification rather than silently complete.
