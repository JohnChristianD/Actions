# Theorem-first canonical learner replication prompt

This is the replication authority. Agda `--safe` proof terms are authoritative. Haskell generation and redundancy auditing are checks, not theorem sources.

## Canonical learner

Source: `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`.

The learner is environment-agnostic and contains Watkins critic-only action selection, deterministic LCB/count memory, fixed-temperature sparsemax, finite negative q-log shaping, learned sparsemax attention, Walsh-labelled recurrent input, hard-sign/Möbius-labelled GRU, explicit F4/L2 optimizer state, NormPair, and a deterministic Nat clock.

The exact direct import surface is **eight** standard-library imports, not seven:

```agda
Relation.Binary.PropositionalEquality
Agda.Builtin.Nat
Data.Nat
Data.Fin
Data.Fin.Properties
Data.Nat.DivMod
Data.Product
Data.Empty
```

The source has no project-local Agda import.

## Default width

The replication default is `d = 64`.

The width constraint is:

`d = 4^k`.

`FiniteParameterCompleteness.agda` proves `learnerDefaultD = 64` and `learnerDefaultD-power4`.

For the present scalar GRU, this is a width specification for the generalized mixing representation, not a claim that the current `GRUState.hiddenState` has already been vectorized to 64 coordinates. A future vectorized implementation must actually change the carrier and its transition functions.

For the Int8 carrier, the exact unnormalized H4 relation is proved by `walshHadamardOrthogonality4`:

`H4 H4ᵀ = 4 I (mod 256)`.

This is orthogonality, not normalized orthonormality. Although `sqrt(4^k) = 2^k`, `2` has no multiplicative inverse in `Z/256Z`. Normalized orthonormality therefore requires an explicit dyadic/rational normalization representation.

## State size

An Int8 scalar has 256 values.

Current GRU storage: 9 Int8 coordinates, `256^9 = 2^72`.

Current GRU + critic + explicit Int8 Walsh carrier: 15 coordinates, `256^15 = 2^120`.

Persistent GRU + critic + Walsh quotient: 14 coordinates, `256^14 = 2^112` equivalence classes, with 256 hidden-state fibres in the current scalar version.

Actual stored `FullLearnerState` Int8 coordinates:

`3 Watkins + 2 attention + 9 GRU + 5 F4 + 2 NormPair + 2 q-log-control = 23`.

Therefore its fixed-Nat, fixed-trace Int8 projection has `256^23 = 2^184` configurations. The entire state is countably infinite because the clock, LCB counts, and finite-rational fields contain `Nat` components.

With only hidden state generalized to width `d`, preserving the remaining scalar layout, the stored Int8 count is `d + 22`, giving `256^(d+22) = 2^(8d+176)` for that finite projection.

## Minimum algebra and library status

The effective algebra is below ring level:

`finite many-sorted data + Nat arithmetic + equality/negation + products/records + End(S)`.

Here `End(S) = S -> S` is the important composition monoid. Identity and function composition supply the associative scan law. A ring, field, module, lattice, metric, or normed-space structure is not required by the maintained learner proofs.

The current learner source directly needs eight standard-library modules because those names are used. Reducing the direct import surface is a separate refactor and must preserve the same `--safe` proof surface.

## L1 and 1-path norm status

The paper `Hidden Synergy: L1 Weight Normalization and 1-Path-Norm Regularization` studies PSiLON-style MLPs and related residual blocks. Its 1-path-norm/Lipschitz results are not automatically theorems about this learner's recurrent sparsemax/Walsh composition.

`FiniteNormAlgebra.agda` therefore defines a deliberately explicit finite test algebra for a two-weight scalar network:

`L1(w) = |w_in| + |w_out|`

`1Path(w) = |w_in| * |w_out|`

with a componentwise `Nat` order and contradiction/equality-zero product lemmas. This is an exact implementation of those finite definitions, not a transcription of the paper's full PSiLON architecture and not a claim that the paper's generalization theorem applies to the learner.

The current learner `NormPair` is still a state record with two `Int8` fields. It must not be described as the PSiLON 1-path norm unless the state transition is changed to compute that actual norm.

## Finite functional parameter completeness

`FiniteParameterCompleteness.agda` proves the exact table-completeness theorem:

for every finite-domain function `f : Fin n -> Fin m`, `parameterizeFin f` represents exactly `f`, pointwise and as a function.

It also proves the generic finite-state-kernel parameter result for arbitrary total finite-component update and choice functions.

This establishes **functional completeness of finite parameter slots**, not universal approximation of unrestricted continuous functions. The fixed learner wiring still constrains how those slots compose.

The arithmetic language can express finite-domain polynomial-like, piecewise-polynomial, threshold/sign, and finite rational-shaped functions. `FiniteRational` remains an encoding record, not a proved division field, so no analytic piecewise-rational completeness theorem is asserted.

## Reachability, controllability, and observability

`CanonicalControlObservability.agda` gives formal definitions and proof terms, but the vocabulary is intentionally narrower than classical control theory because the canonical learner has no external control input.

`CanonicalReachable K s t` means exactly that there exists a natural-number iterate of `canonicalFullStep K` taking `s` to `t`.

`canonicalOrbitReachable` proves every point on the learner's own forward orbit is reachable by its corresponding iterate.

`CanonicalOrbitControllable` is explicitly defined only as reachability of that predetermined orbit. It is **not** Kalman controllability, nonlinear controllability, steering under a free input alphabet, or a practical-control guarantee. The code does not define an external input channel, admissible controls, or a target-set steering problem, so claiming those stronger notions would add assumptions not present in the imports.

For observability, `fullStateObservation s = s`, and `fullStateObservation-injective` proves exact full-state observability. `clockObservation` separately observes the Nat clock, with `clockObservation-after-iterate` proving the exact `clock s + n` law. These are formal identity/clock observation theorems, not a sensor-identification theorem for a hidden environment.

## Environment ports

`CanonicalGamePorts.agda` contains finite executable projections for:

- Jumanji Knapsack
- Jumanji Maze
- Jumanji LevelBasedForaging
- Gymnax MetaMaze
- Gymnax FourRooms
- Gymnax Pong-misc
- Gymnax `MemoryChain-bsuite`
- Gymnax `DiscountingChain-bsuite`
- Gymnax CartPole
- Gymnax Bernoulli-Bandit-misc
- Pobax RockSample

`CanonicalFaithfulGameVariants.agda` additionally preserves the fixed Jumanji Toy Maze wall layout and the exact 13x13 Gymnax FourRooms connectivity predicate.

The upstream Jumanji/Gymnax/Pobax environments include stochastic generation or continuous-valued dynamics in several cases. The canonical Agda ports deliberately choose deterministic finite projections so that they remain within the existing finite/Nat import surface. These are executable structural variants, not claims of bit-for-bit numerical equivalence to JAX floating-point or stochastic sampling.

## The old game regression versus the actual closed loop

The first game-execution regression was an integration smoke test, not an RL trajectory. It used a fixed environment action, passed the resulting reward through `injectReward`, and then executed `canonicalFullStep`.

The maintained theorem `learnerRewardStep-reward-insensitive` now makes the defect explicit:

`learnerRewardStep s r₁ = learnerRewardStep s r₂`.

The canonical autonomous step reconstructs `canonicalSignal` from critic/LCB/clock state and does not read the injected `watkins.signal`. Therefore that old path cannot learn from environment reward. This is an actual structural impossibility result for that wiring, not an impossibility theorem for reinforcement learning in general.

There is a second architectural boundary: the canonical action head is `Sparsemax2Pair = Int8 × Int8`. It is intrinsically a two-action critic head. Four- or six-action environment ports therefore cannot obtain an arbitrary learned action policy from the existing head without an explicit adapter or a generalized action head.

## Closed-loop learner interface

`CanonicalLearnerGameExecution_test.agda` now contains an explicit action-conditioned transition interface:

`encodeActionReward -> decodeAction/decodeReward -> closedLoopCriticUpdate -> closedLoopStep`.

The finite critic target used by this completion is:

`target = reward + 1/2 maxQ`.

The selected action Q-value is updated from that target; LCB counts increment for the actual environment action; reward is also added to the canonical signal used by attention, GRU input, and F4 optimizer input. Exact action/reward encoding round trips and one-step critic-learning facts are proved constructively.

This completes the missing **action/reward plumbing** while leaving the original single-file learner monolith environment-agnostic. The games remain separate modules. It should not be described as an exact DQN or exact negative-Munchausen implementation: the current `negativeFiniteQLog8` record is not consumed by the critic target, there is no target network, and the fixed finite `Int8` target is a bespoke TD-style completion.

## Closed-loop finite benchmark record

The maintained bench records:

`return`, `reference return`, `regret = reference return ∸ return`, `success`, and executed environment steps.

The deterministic finite cases instantiated in the current Agda source are:

| Port | Horizon | Exact return | Reference | Regret | Success | Steps |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Knapsack | 8 | 16 | 16 | 0 | 1 | 5 |
| Maze-v0 projection | 16 | 0 | 1 | 1 | 0 | 16 |
| MetaMaze projection | 16 | 0 | 10 | 10 | 0 | 16 |
| FourRooms projection | 16 | 0 | 1 | 1 | 0 | 16 |
| CartPole quantized projection | 16 | 0 | 0 | 0 | 1* | 16 |
| Bernoulli Bandit, best arm 0 | 16 | 0 | 16 | 16 | 0 | 16 |
| Bernoulli Bandit, best arm 1 | 16 | 16 | 16 | 0 | 1 | 16 |

`*` CartPole “success” here means completing the diagnostic finite horizon because the current quantized port has no terminal condition and zero reward. It is not CartPole balance success.

The regret column is therefore an explicit **reference-policy gap**, not a statistical regret estimator for a stochastic bandit or a claim of regret optimality. The current finite ports are deterministic projections, so these values are exact reductions of the maintained Agda program when the corresponding proofs pass CI.

## Comparison against CleanRL and Gymnax reports

The reference numbers are useful context but are **not apples-to-apples benchmark scores**.

CleanRL's documented classic-control DQN configuration uses a replay buffer, target network, exploration schedule, and a neural action head. Its documented `dqn.py` result for `CartPole-v1` is `488.69 ± 16.11`, with 500,000 training timesteps. CleanRL explicitly describes this as a classic-control DQN benchmark, not an official benchmark from the original DQN paper.

Gymnax's current README reports a CartPole-v1 PPO/ES checkpoint return of `500`, a FourRooms-misc checkpoint return of `1`, a MetaMaze-misc ES checkpoint return of `32`, BernoulliBandit-misc ES return `90`, GaussianBandit-misc ES return `0`, and lists SimpleBandit-bsuite and MNISTBandit-bsuite without a displayed trained-return checkpoint. Those are GPU/JAX baseline reports with upstream numerical/stochastic environment semantics, not the finite deterministic projections used here.

Our current `CartPole` result of `0`, therefore, does not demonstrate that the learner is intrinsically incapable of CartPole learning. It demonstrates that the maintained quantized port has zero reward and no terminal condition, while the completed closed-loop policy remains a two-action finite adapter. A direct comparison requires first replacing that projection by a faithful CartPole state transition and matching the reference action/observation semantics.

Likewise, the Maze/FourRooms/MetaMaze values cannot be read as failures against Gymnax's numbers because the current Agda ports deliberately simplify the dynamics and, for FourRooms, `fourRoomsStep` is currently the generic finite Maze transition rather than the full Gymnax FourRooms environment.

## GameTheory ports

`Exotic/econlib/GameTheory.agda` is deliberately external to the learner monolith. The canonical learner does not import it. It uses **seven** direct standard-library imports and a local `Int8 = Fin 256` encoding, so the old `efficient_chad.Int8` dependency is gone.

The module remains useful for independent theorem tests: Prisoner's Dilemma payoffs, a pure-Nash witness, best-response, stabilization, and finite iteration are explicit and safe. These game-theory modules are test fixtures and theorem-correction surfaces, not hidden learner dependencies.

No current GameTheory source requires a transcendence library. The stale EfficientCHAD-related surface was instead found in an old `CIInterpolation_v147.agda` file whose imported `CompleteSafe_v147` no longer exists. That obsolete v147 interpolation file and its trigger/wake marker files have been pruned from the canonical branch.

## CNN/log-pyramid status

The previous phrase "log-pyramid equivalence" was too strong. The maintained theorem is now an explicit quotient/equality theorem.

`CNNLogPyramid64` is a concrete 64-index code. `cnnToAttention` is its decoder into the learner's attention carrier. `CNNLogPyramidEquivalent p q` is the relation `cnnToAttention p = cnnToAttention q`, and reflexivity, symmetry, and transitivity are proved.

`cnnLogPyramidGRUInputPreservation` proves equal decoded attention implies equal GRU transitions, and `cnnLogPyramidCommutesWithCanonicalGRU` proves that a code whose decoded attention equals the learner's current attention produces exactly the same `canonicalGRUStep`.

This is a representation-factorization/preservation theorem. There is no constructed bijection from an arbitrary CNN architecture, no inverse convolution/pooling map, and no approximation metric or error bound. Consequently the repository makes no claim that the learner's function class exceeds a fixed-depth CNN. Such a statement would require a precisely defined CNN class, input/output domain, parameter constraints, and function metric before it could even be stated as a theorem.

## Hard sparsity

`hardSparse-composition-normPair-F4-L2` is the maximum unconditional sparsity result from the current definitions.

If the canonical policy is already `HardSparseLeft`, replacing NormPair and F4/L2 optimizer state preserves that hard-sparse policy result.

This is a local equality-invariance theorem. It is not a trajectory-wide sparsity guarantee, an analytic L1/path-norm bound, or an arbitrary-state approximation theorem.

## Exact trajectory rank

The exact progress rank is:

`V(s) = clock s`.

`V(canonicalFullStep K s) = V(s) + 1`.

`V(iterateCanonical K n s) = V(s) + n`.

Thus every step is a strict unit increase in the well-order of `Nat`. This requires no environment, reward distribution, statistical, or convergence assumption. It yields no fixed point and no nontrivial finite cycle by contradiction. `totalCount` provides an independent increment-by-one contradiction route.

This is an exact Nat rank, not a classical decreasing Lyapunov function.

## Old-folder pruning

The canonical branch no longer carries the obsolete `MR15Reachability`, `OpenESDyadic`, or `NoisyNetCoupled` learner files. It also no longer carries the broken v147 CI interpolation/trigger/wake markers or the old three-file exploration counterfactual/schema cluster. The generated theorem report remains because the current generator writes it and the workflow checks it.

The external game modules remain modular by design. They are not merged into the learner state or transition function.

## Synchronization and acceptance

The safety scanner covers the canonical learner, game ports, faithful map variants, finite parameter completeness, finite norm algebra, control/observability definitions, CNN preservation, learner execution regression, GameTheory, and generated report.

Current branch acceptance is CI-gated. The closed-loop benchmark theorem surface is considered authoritative only after the current-head Agda workflow has compiled it and its exact metric theorems.