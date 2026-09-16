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

Here `End(S) = S -> S` is the important composition monoid. Identity and function composition supply the associative scan law. A ring, field, module, lattice, metric, or normed-space structure is not required by the maintained proofs.

The current source does need the Agda standard library because it directly imports the eight modules above. The standard library is convenience infrastructure, not the mathematical minimum. A no-stdlib reconstruction is possible only after replacing every actually used primitive and rerunning the same safe theorem surface.

## Finite functional parameter completeness

`FiniteParameterCompleteness.agda` proves the exact table-completeness theorem:

for every finite-domain function `f : Fin n -> Fin m`, `parameterizeFin f` represents exactly `f`, pointwise and as a function.

It also proves the generic finite-state-kernel parameter result for arbitrary total finite-component update and choice functions.

This establishes **functional completeness of finite parameter slots**, not universal approximation of unrestricted continuous functions. The fixed learner wiring still constrains how those slots compose.

The arithmetic language can express finite-domain polynomial-like, piecewise-polynomial, threshold/sign, and finite rational-shaped functions. `FiniteRational` remains an encoding record, not a proved division field, so no analytic piecewise-rational completeness theorem is asserted.

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

The learner execution regression in `CanonicalLearnerGameExecution_test.agda` feeds each port's finite reward through an explicit `Fin 256` reward adapter and then executes `canonicalFullStep`. Thus the learner is checked as an executable interaction loop on every listed port, including the already partially completed CartPole, Bernoulli Bandit, MetaMaze, and RockSample surfaces.

This proves execution and state transition, not empirical sample-efficiency or convergence.

## GameTheory ports

`Exotic/econlib/GameTheory.agda` now uses the same eight direct standard-library imports and no `efficient_chad.Int8` dependency. Its Prisoner's Dilemma payoffs, pure-Nash witness, best-response map, stabilization, and finite iteration theorem remain explicit.

Repository-local search found no active `NoisyNetCoupled`, `OpenESDyadic`, or `MR15Reachability` references in the current canonical branch. Their former remote branch names are also absent from the current branch inventory. They therefore do not belong to the canonical replication surface.

## CNN/log-pyramid preservation theorem

There is now a formal representation-level theorem in `CNNLogPyramidPreservation.agda`.

`CNNLogPyramid64` is an explicit 64-index code. `cnnToAttention` maps that code to the learner's attention carrier. `cnnLogPyramidGRUInputPreservation` proves that equal encoded attention states induce identical GRU transitions, by congruence through the existing attention -> sparsemax -> Walsh -> GRU composition.

`cnnLogPyramidCommutesWithCanonicalGRU` proves:

`cnnToAttention p = attention s`

implies

`cnnLogPyramidGRUStep K s p = canonicalGRUStep K s`.

This is the exact preservation theorem available without inventing an unimplemented CNN convolution/pooling theorem. It says an explicitly encoded 64-level pyramid representation is preserved when its decoded attention state equals the learner's current attention state. It does **not** claim that arbitrary CNN architectures are equivalent to the learner.

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

## Synchronization and acceptance

The safety scanner covers the canonical learner, game ports, exact finite map variants, parameter completeness theorem, CNN preservation theorem, learner execution regression, GameTheory, and generated report.

The theorem generator type-checks those surfaces with `agda --safe` and checks their required theorem names.

The workflow installs Agda 2.8.0 and stdlib 2.4, checks the canonical learner and all maintained regression surfaces, runs the generator and redundancy audit, and then checks the generated report.

A merge to `main` naturally re-runs the same path-based gate because the workflow triggers on the canonical Agda, CI, and documentation paths. No background assumption is needed: synchronization is encoded as repository checks.

The branch must not be described as green until the current PR-head run completes all of those stages successfully.
