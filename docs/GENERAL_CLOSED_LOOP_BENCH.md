# General closed-loop learner bench

## Canonical boundary

`Exotic/ERL/FullCoupled/GeneralFullCoupledLearnerMonolith.agda` is the learner kernel. It is environment-agnostic and uses the finite-action surfaces `QVec A = Fin A -> Int8` and `CountVec A = Fin A -> Nat`.

Default width is `d = 64`, and `powerOfFour64` constructs the witness `64 = 4^3`.

## Sparsemax action arity and proof boundary

The old 2-action interface is no longer the type boundary. `actionSpace2`, `actionSpace4`, and `defaultActionSpace : ActionSpace 64` are all instances of the same `ActionSpace A` interface.

The kernel performs finite score ordering and a largest-valid finite support search and exposes the threshold-style numerator/denominator representation in `SparseWeight`.

This is still **not** the full arbitrary-A Euclidean sparsemax KKT/simplex theorem. The remaining proof obligation is the algorithm-to-KKT arithmetic bridge: the selected support must be shown to satisfy positivity on the active set, non-positivity outside it, normalization, and the corresponding KKT stationarity/complementarity equations. No postulate or theorem shell is used to conceal that gap.

`Data.Fin` is the essential finite-index convenience. `Data.Nat.Properties` is now a direct import in the monolith because the later exact finite arithmetic proofs are substantially clearer with standard Nat order, associativity, commutativity, and distributivity lemmas. A commutative semiring-with-no-zero-divisors is not a required carrier for the Int8 layer and would be the wrong abstraction for modulo-256 arithmetic. Vector/list functional modules and sort-property bundles remain optional conveniences until the KKT proof needs their exact permutation/sortedness lemmas.

## Closed-loop semantics

The intended loop is:

`learner state -> generalPolicy -> finite action -> modular game step -> reward/next game state -> learnerStep -> next learner state`.

`GeneralClosedLoopBenchV2.agda` implements that learner-selected loop and records exact finite values:

- `return`: cumulative encoded reward,
- `regret`: `referenceReturn - return` under Nat subtraction,
- `success`: terminal-success bit,
- `steps`: actual transitions executed.

The ordinary `AblationPair` keeps the environment, horizon, initial state, action space, optimizer, GRU, NormPair, and reward adapter fixed while changing only `MunchausenMode`.

`NegativeQMunchausenBench.agda` adds the requested ceteris-paribus **negative-Q-Munchausen vs no-Q-Munchausen** path. The shaping term is explicitly `Int8` negative-Q shaping, not a claim of equivalence to the standard floating-point `alpha * log pi` Munchausen formula.

## Trace-valued Mobius/GRU coupling

`MobiusTrace.agda` introduces a `Nat -> MobiusAction` trace, so each depth may carry a different Mobius action. `prefixAction` is the associative scan over those actions, and `traceGRU-step-law` ties the prefix composition directly to the iterated `gruStep`. `trace-depth-invariant` then lifts the existing persistent-token invariant through the whole depth trace.

This is the algebraic connection that was missing when Mobius composition and GRU persistence were proved independently.

## Environment suite

The current closed-loop suite keeps CartPole, BernoulliBandit, MetaMaze, FourRooms, Jumanji Knapsack, LevelBasedForaging, Pong, MemoryChain, DiscountingChain, and POBAX T-Maze.

RockSample and the Jumanji Maze-v0 path are intentionally excluded from this suite.

`AdditionalBenchmarkPorts.agda` adds a deterministic uniform-bandit projection and a finite Game2048 projection with the four directional actions. The Gaussian reward semantics of the Gymnax reference are intentionally replaced by a uniform finite reward cycle for the formal benchmark, rather than importing Gaussian arithmetic or randomness into the learner.

The 2048 port is explicitly a finite projection of the Jumanji/Pgx action contract, not a claim that the monolith contains the full 4x4 board implementation.

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

The Agda source records the result objects and exact metric definitions, but this execution environment has no local Agda executable and the development branch has not yet returned a GitHub Actions proof run. Therefore there are **no verified observed return/regret/success/steps numbers** to report for either ordinary Munchausen or negative-Q-Munchausen. Reporting numeric outcomes now would be fabrication.

The authoritative outputs to record after the external Agda run are the concrete `LoopResult` values from `GeneralClosedLoopBenchV2` and the concrete `QMunchausenAblation` values from `NegativeQMunchausenBench`.

## CNN theorem boundary

The learner contains no CNN component. `ExternalCNNTransitionBisimulation.agda` remains the minimal external adapter chain:

`ExternalCNN.encode -> RepresentationAdapter.decode -> LearnerTransition.input -> next-state`.

`StandardCNNComparison.agda` strengthens that boundary using an abstract `FiniteDepthMachine`, a translation action, an explicit convolutional equivariance law, depth agreement, and transition preservation. It contains no convolution kernel, stride, padding rule, tensor layout, trained weights, or executable CNN.

That shape is consistent with the formal-neural-network literature's use of abstract finite-depth machines to cover convolutional and recurrent architectures while keeping the architecture itself separately instantiated. It gives a theorem target for CNN equivalence without smuggling a concrete CNN into the learner semantics.

## Evidence status

No local Agda compiler is present in this execution environment. The branch workflow remains the external Agda proof oracle. Until a development-branch run returns success, new generalized theorem modules and benchmark modules remain pending external typecheck rather than silently treated as complete.
