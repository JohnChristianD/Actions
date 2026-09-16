# General closed-loop learner bench

## Canonical boundary

`Exotic/ERL/FullCoupled/GeneralFullCoupledLearnerMonolith.agda` is the learner kernel. It is environment-agnostic and uses the finite-action surfaces `QVec A = Fin A -> Int8` and `CountVec A = Fin A -> Nat`. Environment definitions remain external in `CanonicalGamePorts.agda`.

Default width is `d = 64`, and `powerOfFour64` constructs the witness `64 = 4^3`.

## Sparsemax action arity

The old 2-action interface is no longer the type boundary. `actionSpace2`, `actionSpace4`, and `defaultActionSpace : ActionSpace 64` are all instances of the same `ActionSpace A` interface.

The kernel performs finite score ordering and a finite support-size search and exposes the exact threshold-style numerator/denominator representation in `SparseWeight`. The closed-loop action selector currently uses the maximal sorted score, so the repository must not describe this as a fully proved Euclidean sparsemax projection until the KKT/simplex normalization theorem is added and typechecked.

`Data.Fin` is the essential finite-index convenience. A commutative semiring-with-no-zero-divisors is not required and would in fact describe the wrong arithmetic carrier for modulo-256 Int8, which has zero divisors. `Data.Nat.Properties`, vector/list functional modules, semiring property bundles, and sorting libraries are optional proof conveniences rather than logical necessities of the present kernel.

## Closed-loop semantics

The intended loop is:

`learner state -> generalPolicy -> finite action -> modular game step -> reward/next game state -> learnerStep -> next learner state`.

`GeneralClosedLoopBenchV2.agda` now implements that learner-selected loop and records exact finite values:

- `return`: cumulative encoded reward,
- `regret`: `referenceReturn - return` under Nat subtraction,
- `success`: terminal-success bit,
- `steps`: actual transitions executed.

The Munchausen and no-Munchausen pair uses the same environment, horizon, initial learner state, action space, action decoder, optimizer, GRU, NormPair, and reward adapter. Only `MunchausenMode` changes.

These are deterministic finite projections. They are not numerically interchangeable with floating-point/stochastic Gymnax when an upstream environment uses continuous dynamics, transcendental functions, or random resets.

## Environment suite

The bench instantiates CartPole, BernoulliBandit, MetaMaze, FourRooms, Maze, Jumanji Knapsack, LevelBasedForaging, Pong, MemoryChain, DiscountingChain, and Pobax RockSample through external modular ports.

The formal learner does not import those game modules. Only the benchmark adapter imports the game ports.

## Gymnax published reference points

Gymnax's current README lists checkpoint returns of:

- CartPole-v1: `500`
- BernoulliBandit-misc: `90`
- MetaMaze-misc: `32`
- FourRooms-misc: `1`
- MemoryChain-bsuite: `0.1`
- DiscountingChain-bsuite: `1.1`

The same table lists Pong-misc without a checkpoint return. Gymnax says its displayed throughput figures are estimated for 1M random-policy transitions on an NVIDIA A100 using JIT-compiled episode rollouts with 2000 workers. Those figures are not used as claims about this Agda learner.

The Gymnax README also describes its functional rollout pattern as policy action selection followed by `env.step`, with complete episode loops expressible through `jax.lax.scan`. That is the closest execution-level comparison with the Agda closed-loop interface.

## Munchausen ablation

`AblationPair` contains `plain` and `munchausen` runs from exactly the same initial state and horizon. A usefulness statement is valid only after the current Agda gate has typechecked the benchmark and the exact `LoopResult` values have been observed. No statistical aggregation is encoded in the formal source.

## CNN theorem boundary

The learner contains no CNN component. `ExternalCNNTransitionBisimulation.agda` defines the minimal external adapter chain:

`ExternalCNN.encode -> RepresentationAdapter.decode -> LearnerTransition.input -> next-state`.

The proven content is representation-equality propagation through the learner input map and arbitrary next-state map. A stronger bisimulation theorem requires a relation on external CNN representations that is preserved by the representation map and learner transition; an approximate version additionally needs an explicit metric/pseudometric and error bound.

For theorem-level comparison, a finite CNN should be specified independently as a finite composition of shared local linear/convolution operators, pointwise nonlinearities, and optional stride/pooling/readout operators. This keeps CNN structure external to the learner while making any later function-class theorem precise.

## Evidence status

No local Agda compiler is present in this execution environment. The branch workflow has therefore been configured to run on the development branch itself, allowing Agda 2.8.0 + stdlib 2.4 to be the external proof oracle. Until that branch run returns success, the generalized sparsemax and closed-loop benchmark are pending external typecheck rather than silently treated as complete.
