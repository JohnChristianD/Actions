# Theorem-first canonical learner replication prompt

This file is the replication authority. Agda `--safe` proof terms are authoritative; generated reports and redundancy audits are verification helpers.

## Canonical learner

Current generalized learner source:

`Exotic/ERL/FullCoupled/GeneralFullCoupledLearnerMonolith.agda`

It is environment-agnostic and defines the finite-action learner interface, LCB/count memory, finite sparsemax threshold representation, negative Munchausen mode, hard-sign GRU, Möbius endomorphism composition, F4/L2 optimizer state, NormPair, finite functional parameter identity, and the exact Nat clock rank.

The current direct import surface is eight modules:

```text
Relation.Binary.PropositionalEquality
Agda.Builtin.Nat
Data.Nat
Data.Fin
Data.Fin.Properties
Data.Nat.DivMod
Data.Product
Data.Empty
```

`Data.Fin` is the essential finite action index. No commutative-semiring/no-zero-divisor bundle is logically required. Modulo-256 arithmetic itself has zero divisors, so a no-zero-divisor algebra would describe a different carrier.

## Default width

The default is `d = 64`.

```text
64 = 4^3
```

`PowerOfFour` and `powerOfFour64` prove this constructively.

The current GRU carrier remains scalar Int8; the width witness is a generalized representation constraint, not a false claim that `GRUState.hiddenState` already has 64 coordinates.

## General-action sparsemax boundary

`QVec A = Fin A -> Int8` and `CountVec A = Fin A -> Nat` remove the old two-action type bottleneck. `actionSpace2`, `actionSpace4`, and `defaultActionSpace : ActionSpace 64` instantiate the same interface.

The current kernel performs finite score ordering and an exact sparsemax-style support/numerator calculation. The policy execution path presently chooses the maximum sorted action. Therefore the interface is genuinely general in `A`, while a full Euclidean sparsemax KKT/simplex-normalization theorem is still a separate proof obligation. The repository does not call the current selector a completed arbitrary-A Euclidean sparsemax theorem.

This deliberate separation keeps the benchmark executable without smuggling a false normalization theorem into the Agda proof kernel.

## Closed-loop benchmark

`Exotic/ERL/FullCoupled/GeneralClosedLoopBenchV2.agda` keeps games external and drives the learner in the actual closed loop:

```text
learner state
  -> generalPolicy
  -> action
  -> game step
  -> reward + next game state
  -> learnerStep
  -> next learner state
```

`LoopResult` records exact finite values:

- `return`
- `regret`
- `success`
- `steps`

`AblationPair` runs identical initial state, horizon, action space, game transition, reward adapter, GRU, optimizer, NormPair, and learner state, with only `MunchausenMode` changed.

No statistical aggregation is part of the formal source.

## Game modularity

The learner monolith does not import game modules. `CanonicalGamePorts.agda` remains the independent external environment surface. Current benchmark adapters include CartPole, BernoulliBandit, MetaMaze, FourRooms, Maze, Jumanji Knapsack, LevelBasedForaging, Pong, MemoryChain, DiscountingChain, and RockSample.

The Agda ports are finite deterministic projections. They should not be called bit-for-bit Gymnax/Jumanji reproductions when upstream dynamics use random resets, floating-point trigonometry, continuous state, or environment-specific random keys.

## Gymnax reference points

Gymnax's current README reports checkpoint returns of 500 for CartPole-v1, 90 for BernoulliBandit-misc, 32 for MetaMaze-misc, 1 for FourRooms-misc, 0.1 for MemoryChain-bsuite, and 1.1 for DiscountingChain-bsuite. Pong-misc has no checkpoint return in that table. Gymnax says its displayed throughput values are estimated for 1M random-policy transitions on an NVIDIA A100 with 2000 workers.

Those numbers are external reference points, not measurements of this Agda learner. Cross-implementation comparison is meaningful only after matching environment dynamics, horizon, action semantics, reward coding, state representation, initialization, and training procedure.

## CNN theorem boundary

The learner contains no CNN component.

`Exotic/ERL/FullCoupled/ExternalCNNTransitionBisimulation.agda` defines the minimal external comparison chain:

```text
ExternalCNN.encode
  -> RepresentationAdapter.decode
  -> LearnerTransition.input
  -> next-state
```

`CNNEquivalent` is decoder-induced representation equality. `externalCNN-transition-preserves` proves that equal decoded representations produce equal learner inputs. `cnn-bisimulation-step` transports that equality through an arbitrary next-state map.

This theorem gives a practical quotient: any two external representations that decode to the same learner input are indistinguishable by the subsequent learner transition. It does not claim a CNN is part of the learner.

For a theoremic CNN comparison, use an explicitly external finite CNN model class. A standard formal contract is a finite composition of shared local linear/convolution operators, pointwise nonlinearities, optional stride/pooling operators, and a readout. Vertechi and Bergomi's *Machines of finite depth* supplies a useful formal architecture framework that treats convolutional and recurrent networks as compositional finite-depth machines; Jiang and Zavala provide a mathematical CNN foundations treatment emphasizing grid data and learned convolution operators.

A genuine CNN-vs-learner function-class theorem still needs an explicit input/output domain, architecture/depth/width bounds, parameter domain, and exact or approximate equality metric. No such class-separation claim is made here.

## L1 / 1-path norm status

`FiniteNormAlgebra.agda` provides exact finite definitions for a two-weight test network. The current `NormPair` learner field is a state record and is not silently identified with the PSiLON 1-path norm.

SciSpace's *Hidden Synergy: L1 Weight Normalization and 1-Path-Norm Regularization* studies PSiLON-style MLPs and its own Lipschitz/generalization arguments. Those hypotheses do not automatically transfer to the GRU+sparsemax/Walsh/F4 composition.

## Algebraic minimum

The computational skeleton is:

```text
finite carrier + lookup/equality/order
+ Nat arithmetic for sizes/ranks
+ endomorphism composition
```

The scan algebra is the monoid `End(S)` under ordinary composition. A ring/field is unnecessary for that theorem.

The finite Mobius encoding uses numerator/denominator data with Nat cross-multiplication. For `x` in an Int8 code space, `1 + (255 - x)` is the denominator encoding `256-x`; positivity follows from the finite bound. A real-field theorem is not asserted.

Walsh mixing can remain a finite lookup-table construction. The H4 relation is an unnormalized Gram law modulo 256; normalized orthonormality requires a separate dyadic/rational normalization carrier because 2 is not invertible modulo 256.

Pareto reasoning needs only product ordering over finite objective tuples, not a semiring property bundle.

`Data.Vec.Functional`, `Data.List.Sort`, `Data.List.Properties`, `Data.Nat.Properties`, and `Algebra.Properties.Semiring` remain optional convenience libraries. They are not required by the current direct import surface.

## Exact trajectory order

The learner's exact rank is:

```text
V(s) = clock s
V(step s) = V(s) + 1
V(iterate n s) = V(s) + n
```

So `Nat` gives a strict unit-progress order with no fixed point or nontrivial finite cycle. This theorem needs no environment, statistical, reward-distribution, or convergence assumptions.

It is an increasing Nat rank, not a classical decreasing Lyapunov function.

## Acceptance gate

The repository workflow installs Agda 2.8.0 and stdlib 2.4 and compiles the generalized learner, closed-loop benchmark, external CNN theorem, legacy maintained theorem surfaces, game ports, regression fixtures, generated report, and redundancy audit.

The development branch is configured as a push-trigger target because the GitHub connector cannot create a new pull request or dispatch a manual run from this environment. The current branch must therefore be considered **pending external Agda verification** until GitHub reports a fresh run for the current head.
