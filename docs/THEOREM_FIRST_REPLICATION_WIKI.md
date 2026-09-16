# Theorem-first canonical learner replication prompt

This file is the replication authority for the canonical learner specification. Agda `--safe` proof terms are authoritative. Haskell discovery and redundancy auditing are automation only.

## Canonical source

`Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

The canonical file has no project-local Agda imports. It contains the endogenous learner composition only: Watkins critic, LCB count correction, fixed-temperature sparsemax, finite negative q-log shaping, learned sparsemax attention, Walsh-labelled recurrent input, custom hard-sign/Möbius-labelled GRU, F4/L2 optimizer, NormPair, q-log state, and deterministic clocked transition.

No environment, reward process, replay buffer, probability space, posterior sampler, statistical-limit assumption, or convergence certificate is part of the canonical state.

## Replication constraints

1. Keep the canonical learner environment-agnostic.
2. Keep the Watkins critic as the sole canonical action-selection source.
3. Attention may affect the recurrent representation but must remain policy-invariant.
4. Preserve the explicit F4 optimizer state and global L2 correction in the complete state.
5. Preserve `NormPair` with its `l1` and `path` coordinates and derived `+1` weight.
6. No holes, postulates, wildcard proof terms, or hidden theorem premises.
7. Derive unconditional facts by definitional equality, contradiction, negation, substitution, or induction over existing finite/Nat structure.
8. Do not silently promote finite constructors into real-analysis theorems.
9. Do not describe the current Walsh code as fully orthonormal unless the exact matrix law has actually been proved.
10. Treat the imports below as the convenience proof surface to minimize only after proving replacements compile.

## `d` and the Walsh-Hadamard constraint

The intended recurrent mixing width `d` is constrained to powers of four:

`d = 4^k`, for `k : Nat`.

This makes the normalized Walsh-Hadamard coefficient scale dyadic because

`sqrt(d) = 2^k`.

There is, however, an important representation distinction:

- the unnormalized Walsh-Hadamard matrix satisfies `H_d H_d^T = d I`;
- the normalized matrix is `W_d = 2^(-k) H_d`;
- `2^(-k)` is not an internal inverse of `2` in the modular carrier `Z/256Z`, so exact normalized orthonormality cannot be claimed merely by saying the width is a power of four;
- exact normalized orthonormality requires an explicit dyadic/rational representation and a corresponding inner-product proof, while an Int8 implementation can still use the integer Hadamard transform plus an explicitly represented normalization boundary.

The current monolith's `HalfInt` stores a natural numerator only, and its current `walshOrthonormal` theorem proves the diagonal self-dot values `4,2,2,2` for the present rows. It does not prove `H4 H4^T = 4I`, and it does not establish a normalized orthonormality theorem over the Int8 modular carrier.

The current four-coordinate mixing block is width `4 = 4^1`. Do not infer a general `d = 4^k` implementation from the scalar GRU state merely by notation. A true variable-width implementation must vectorize the hidden carrier and define the corresponding Hadamard layer.

## Exact state-size accounting

`Int8` wraps `Fin 256`, so each stored Int8 scalar has exactly `256 = 2^8` values.

### Current GRU storage

`GRUState` stores nine Int8 scalars:

- hidden state: `1`;
- recurrent matrix coordinates: `3`;
- recurrent noise coordinates: `3`;
- global optimizer/L2 control coordinates: `2`.

Thus the current purely-Int8 GRU projection has

`256^9 = 2^72`

configurations.

### Current GRU + critic + explicit Walsh carrier

`GRUCriticWH8State` stores `9 + 2 + 4 = 15` Int8 coordinates, hence

`256^15 = 2^120`.

The persistent quotient fixes `8` GRU persistent coordinates, `2` critic coordinates, and `4` Walsh coordinates, hence `14` Int8 quotient coordinates:

`256^14 = 2^112` equivalence classes,

with `256 = 2^8` hidden-state fibres in the current scalar implementation.

### Actual complete `FullLearnerState`

The full learner does **not** store the four Walsh coordinates as a field. They are computed transiently in `canonicalGRUStep`. The actual stored Int8 coordinates are:

- Watkins: critic `2` + signal `1` = `3`;
- attention: `2`;
- GRU: `9`;
- F4 optimizer: `5`;
- NormPair: `2`;
- q-log control: `2`.

Total current stored Int8 coordinates:

`3 + 2 + 9 + 5 + 2 + 2 = 23`.

Therefore the fixed-Nat, fixed-trace Int8 slice has `256^23` Int8 configurations, with one additional Boolean-like trace coordinate.

The **entire** `FullLearnerState` is not a finite state space, because `clock`, the three LCB counts, and the three fields of `FiniteRational` are `Nat`-valued and therefore unbounded. Its cardinality is countably infinite. The finite `256^(...)` counts are only for the Int8 projection.

### Width-`d` bookkeeping under the current storage layout

If only `hiddenState` is generalized to a `d`-coordinate Int8 vector while the eight persistent GRU scalars, Watkins, attention, F4, NormPair, and q-log-control coordinates retain their current scalar layouts, the stored Int8 coordinate count becomes

`d + 22`.

Thus the finite Int8 projection has

`256^(d + 22) = 2^(8d + 176)`

configurations, apart from the separate Boolean trace factor and the unbounded Nat fields.

This formula is the actual full-composition count under the current record layout. It is not the earlier `d + 14` GRU+critic+Walsh quotient count.

## Minimum exclusive algebra actually used

The effective proof/program surface is substantially below ring algebra.

At the carrier level the canonical file uses only:

- `Nat` with `zero`, `suc`, addition, multiplication, truncated subtraction, and the finite less-than tests needed by the definitions;
- `Fin 256` and conversion to/from bounded naturals;
- equality, disequality, substitution, symmetry, congruence, transitivity, and `⊥` for contradiction;
- products for finite tuples and records;
- ordinary total functions between the state carriers.

The modular Int8 operations are computationally induced by reduction modulo `256`, so the carrier can be identified mathematically with `Z/256Z`. But the maintained theorem surface does not require a declared ring, semiring, field, module, vector space, lattice, metric space, or normed space.

The strongest actual composition law is the endomorphism monoid:

`End(S) = S -> S`

with identity and ordinary function composition. Its associativity is the exact law used by `GRUAction`, input actions, and the Möbius-labelled scan. This is the minimal algebraic structure for the scan layer.

So the useful hierarchy is:

`finite many-sorted data + finite arithmetic primitives + equality/negation + endomorphism monoid under composition`.

A ring is a semantic interpretation of part of the carrier, not a required theorem premise.

## Do you need the Agda standard library?

For the **current source as written**, yes. The direct imports are standard-library modules:

`Relation.Binary.PropositionalEquality`, `Data.Nat`, `Data.Fin`, `Data.Fin.Properties`, `Data.Nat.DivMod`, `Data.Product`, and `Data.Empty`.

The current definitions use those modules directly, so a replication of the current file needs the standard library. The CI currently verifies against Agda `2.8.0` and stdlib `2.4`.

For a mathematically minimal implementation, no: the model can be rebuilt using only Agda built-ins plus small local replacements for finite naturals, `Fin`, modulo, products, and the few equality/contradiction lemmas actually needed. That would be a source refactor, not a different theorem assumption.

The current imports are therefore **not minimally exclusive at module-closure level**. CI's import trace shows broad transitive closure through algebra, lattice, relation, function-metric, induction, and related infrastructure even though the canonical file does not use those abstractions as theorem assumptions. The current imports are convenience-oriented, not minimal.

## Watkins + sparsemax + LCB

`canonicalPolicy` depends on the Watkins critic and LCB count state, then applies the fixed-temperature sparsemax carrier. Learned attention is deliberately absent from action selection.

The implementation has exact finite regression laws for the temperature surface and the finite LCB bonus table. No continuous confidence theorem or statistical calibration claim is inferred from those constructors.

## Negative q-log / Munchausen-style boundary

`finiteQLog8` and `negativeFiniteQLog8` are finite rational-shaped records. They are constructor-level finite encodings, not a theorem of real logarithms or division.

`canonicalQLogControlStep` derives its coefficient from the current policy, and `canonicalQLogStep` stores the resulting finite carrier.

## GRU quotient and associative composition

`GRUEquivalent s t` is equality of the persistent GRU projection. `persistent-preservation` keeps recurrent matrices, noise, and global optimizer/L2 control fixed under a GRU step. `gruStep-respects-equivalence` therefore makes the transition well-defined on the quotient.

`GRUAction` is the endomorphism carrier `GRUState -> GRUState`. `composeGRUAction` is ordinary function composition, and `gruActionAssociativity` is definitional equality. The scan theorems regroup operators without changing input order.

This is why the algebra is below ring level: the important multiplication is composition of functions, not multiplication of state vectors.

## Hard sparsity under NormPair + F4 + coupled L2

`NormPair` contains the `l1` and `path` coordinates. `normPairWeightPlusOne` computes their derived `+1` carrier. `F4IntUState` contains five Int8 optimizer coordinates, while `F4IntUKernel.globalL2` feeds the optimizer's explicit L2 correction.

`hardSparse-composition-normPair-F4-L2` proves:

if the current canonical policy is already `HardSparseLeft`, replacing the NormPair and optimizer state leaves that policy result in `HardSparseLeft`.

This is the maximum unconditional statement available from the current definitions. It is a **local structural invariance theorem**. It is not a trajectory-wide lower/upper bound on a sparsity ratio, not an analytic L1/path penalty theorem, and not a guarantee that arbitrary Watkins/LCB evolution never crosses a sparsemax boundary.

The current source also does not contain a theorem that every arbitrary state can be approximated while remaining in a hard-sparse class. Such a result would require an explicit metric, approximation relation, parameterization completeness theorem, and preservation theorem for that approximation relation.

## What arbitrary functions are actually representable?

The canonical kernel records contain higher-order function fields such as critic updates, greedy decisions, trace updates, attention updates, attention-to-GRU maps, optimizer updates, and LCB bonuses. Since several of these are arbitrary total functions at finite component types, the kernel can parameterize arbitrary finite-component transition behaviour subject to the fixed wiring of `canonicalFullStep`.

That is the correct completeness statement. The current source does **not** prove that the complete learner is a universal approximator for every arbitrary function from an unrestricted state space.

For the arithmetic expression language actually present, ordinary finite case analysis plus `+`, `*`, truncated subtraction, comparisons, signs, and finite encoded rational-shaped records can represent finite-domain polynomial-like, piecewise-polynomial, threshold/sign, and piecewise finite-rational-shaped functions. There is no transcendental primitive in the canonical arithmetic surface.

Do not upgrade this observation to a theorem of analytic piecewise-rational universal approximation. `FiniteRational` is an encoding record, not a field with proved division laws, and the source has no transcendental completeness theorem.

## CNN log-pyramid question

There is currently no theorem that a CNN log-pyramid can be expressed by the full coupling. The canonical source contains no convolutional tensor type, spatial indexing hierarchy, pooling law, receptive-field theorem, or logarithmic pyramid encoding.

What can be stated is only the architectural analogue: attention produces a representation, the Walsh-labelled layer mixes it, and the GRU consumes the result. A formal CNN/log-pyramid equivalence would require an explicit representation map and preservation/equivalence theorem.

## Exact Lyapunov/rank order and inevitable cycle exclusion

The natural exact progress rank is

`V(s) = clock s`.

The canonical step satisfies

`V(canonicalFullStep K s) = V(s) + 1`.

Iteration satisfies

`V(iterateCanonical K n s) = V(s) + n`.

This is an exact **strict Nat rank of unit order**. It is not a classical Lyapunov-decrease theorem, because the value increases rather than decreases, and no environment or statistical assumptions are involved.

Consequences proved purely by contradiction/negation are:

- no fixed point;
- no one-step return;
- no nontrivial finite cycle;
- no orbit point can equal its own successor;
- `totalCount` independently increases by exactly one, yielding a second contradiction route for counted cycles.

Because `clock` is unbounded, this rank is `omega`-ordered rather than a finite ranking over the complete learner state. The finite Int8 subprojection does not change that: the explicit Nat clock prevents a deterministic full-state cycle.

## Literature-algebra correspondences

The implementation is best described as an endomorphism-composition learner with a persistent recurrent quotient. Adjacent literature includes:

- Martin and Cundy, *Parallelizing Linear Recurrent Neural Nets Over Sequence Length*, arXiv:1709.04057. The shared idea is associative regrouping for recurrence evaluation; the present GRU is not thereby a linear recurrence. https://arxiv.org/abs/1709.04057
- Maleki and Burtscher, *Automatic Hierarchical Parallelization of Linear Recurrences*, ASPLOS 2018. The correspondence is parallelizable recurrence composition, not identical arithmetic. https://doi.org/10.1145/3173162.3173168
- Ali, Zimerman, and Wolf, *The Hidden Attention of Mamba Models* (2024). Useful scan/attention context, not an equivalence claim. https://arxiv.org/abs/2403.01590
- KalMamba (2024). Relevant to associative state-space scanning in RL, but with different transition algebra. https://arxiv.org/abs/2406.15131
- Weissenborn and Rocktäschel, *MuFuRU: The Multi-Function Recurrent Unit* (2016). Closest architectural analogy for gated functional composition. https://arxiv.org/abs/1606.03002
- Jones, Swan, and Giansiracusa, *Algebraic Dynamical Systems in Machine Learning* (2024). Closest broad algebraic-dynamics framing. https://doi.org/10.1007/s10485-023-09762-9

These correspondences do not establish equivalence to a standard GRU, Mamba, SSM, Transformer, SSRN, or a ring-valued neural architecture.

## Branch and module pruning policy

The canonical branch is `agda-theorem-first-monolith-20260916`. The currently enumerated remote branches do not contain branch names matching `Noisy Nets`, `OpenES`, or `MR15`; no such remote refs are present in the current branch inventory. They therefore have no active branch head to preserve in the canonical replication surface.

The redundancy audit is `.ci/discovery/PruneRedundantLearnerModules.hs`. Its default mode is dry-run and `--apply` removes only modules with zero repository-local import users. Keep the canonical Agda monolith and the regression/test/generator surfaces synchronized with any future pruning.

## CI and acceptance

The current workflow installs Agda `2.8.0` and stdlib `2.4`, rejects forbidden theorem families/holes/postulates first, then type-checks the canonical learner before regression, generation, and redundancy steps.

The latest recorded gate for commit `d270eb0772b83215b1e54111eadcfc2ad334c1c7` failed at `canonicalFullStep-clock`: the proof used `plus-zero` in a place where the target was already definitionally reflexive. The source currently has the more direct target around `clockAfter`, but the gate must be rerun against the exact commit after fixing `canonicalFullStep-clock` itself.

Therefore the replication status must not be described as green until a fresh gate type-checks the canonical source and then completes regression, generation, redundancy, and generated-report validation.

## Maintained negative claims

The canonical surface does not establish:

- convergence to `Q*` for arbitrary environments;
- almost-sure, expected, or stochastic convergence;
- LCB confidence calibration;
- posterior-sampling equivalence;
- regret or global optimality;
- Nash/Pareto/minimax equivalence;
- full H4 orthogonality for the current Walsh rows;
- a continuous-real rational-division implementation;
- a global analytic L1/path norm theorem;
- arbitrary-function universal approximation over unrestricted domains;
- CNN log-pyramid equivalence;
- trajectory-wide hard-sparsity preservation without an explicit boundary-invariance premise.

The strongest theorem-first replication prompt is therefore: preserve the exact finite executable definitions, prove only what follows by deduction from them, keep the algebra at the endomorphism-composition level rather than importing ring assumptions, and make every stronger claim conditional on a new explicit representation theorem rather than smuggling in an outside assumption.
