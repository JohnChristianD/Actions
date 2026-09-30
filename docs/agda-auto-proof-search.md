# Agda proof search in this repository

## Proof authority

The repository has exactly two tracked Agda authority files:

- `FullCoupled/CanonicalLearnerMonolith.agda`
- `FullCoupled/TheoremsMonolith.agda`

Interactive proof search is a construction aid. An accepted Agda term is the authority. Mercury, Dhall, Mirth, Nix, Elm, SMT output, Vehicle output, and JAX execution are supporting layers.

## Left inverse and injectivity

The canonical GRU statistical observation contains the original `GRUState`, and its decoder returns that state by first projection.

The explicit proof chain is:

`canonicalGRUStatisticalDecodeEncode` → `canonicalGRUStatisticalEncodeLeftInverse` → `leftInverse-implies-injective` → `canonicalGRUStatisticalEncodeInjective`.

The packaged theorem is `CanonicalGRUStatisticalInjectivityTheorem`.

This establishes injectivity of the observation encoding. It does not establish injectivity of `gruStep`.

## Tail stability and the convergence kernel

The canonical learner proves persistence of its matrix/noise/control GRU tail under one step and carries the fact through full-learner iteration.

`GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem` is a generic composition kernel. It explicitly requires:

- injective encoding;
- exact state/feature step conjugacy;
- an eventually fixed feature tail.

It derives a tail-fixed source state, eventual stationarity, and identifiability from those premises. The theorem does not manufacture domain-specific physics, economics, or Baird witnesses.

## Canonical Baird boundary

Generic arbitrary Baird records are not part of the active surface.

The concrete declaration is `CanonicalLearnerBairdSevenStarBoundary K s`, indexed by the actual canonical learner. It fixes the seven-state/eight-feature setup, behavior probabilities, solid target, zero reward, discount factor, feature equations, and the already-proven persistent-GRU iterate tail.

The divergence statement remains an explicit witness at that boundary. This is a canonical-learner Baird construction, not a universal Baird theorem.

## Hidden-Synergy L1 and 1-path norm

The active theorem surface retains a finite formal layer for the hidden-synergy regularization structure:

`rowL1`, `weightL1`, `onePathVector`, `onePathNorm`, `rowL1OnesAbs`, `onePathOneLayer`, `HiddenSynergyNormPair`, and `layerNormPair`.

The exact one-layer theorem is `hiddenSynergy-one-layer-exact`.

The paper-faithful near-sparsity discussion is kept conceptually separate from Tsallis-2: the original paper uses Shannon-entropy near-sparsity while this repository also records an exact finite Tsallis-2 extension. citeturn219666academia0

## Degenerate hard sparsity and Tsallis-2

The canonical learner still supplies the exact zero-threshold sparse equivalence:

`HardSparse K s` ↔ `SoftSparseBounded K s zero`.

The theorem monolith packages this as `CanonicalHardSparsityDegeneracyTheorem`.

The generalized finite Tsallis-2 layer contains:

`ActionWeights`, `actionSupportCount`, `actionWeightSum`, `actionWeightSquareSum`, `generalTsallis2Denominator`, `generalTsallis2Numerator`, `generalTsallis2NearSparsity`, `generalTsallis2NearSparsity-zero`, `generalTsallis2NearSparsity-definition`, `generalSupportSparsity`, and `UniformSupportTsallisBoundary`.

The finite quantity is represented exactly as a rational numerator/denominator pair, with an explicit zero-vector convention. The support boundary is kept as its own theorem record.

Continuous Shannon, Lipschitz, differentiability, or convexity conclusions are not inferred from those finite equalities.

## PPAD boundary

There is no PPAD-completeness theorem.

A valid PPAD result needs a concrete polynomial-size total search relation, membership, size bounds, and a hardness reduction. Fixed-point or equilibrium vocabulary alone does not discharge those proof obligations.

## JAX reproof surface

The dedicated JAX program currently contains:

- `vmap_affine`
- `associative_prefix_sum`
- `recurrent_scan`
- `lexicographic_score_order`
- `sparse_support_size`
- `sparse_support_top_k`
- `sparsemax_policy_index`
- `l1_row`
- `l1_matrix`
- `one_path_norm`
- `tsallis2_near_sparsity_fraction`
- `support_sparsity_fraction`
- `integer_layernorm_centered_numerators`
- `integer_layernorm_radicand`
- `batched_integer_layernorm_radicand`
- `signed_gate`
- `gru_hidden_step`
- `batched_gru_hidden_step`
- `jitted_scan_sum`

The theorem monolith has a named Agda counterpart for each of them, all collected in `JAXExecutionMirrorReproof`.

The additional sparsity mirrors are:

- `jaxL1Row`
- `jaxL1Matrix`
- `jaxOnePathVector`
- `jaxOnePathNorm`
- `jaxTsallis2NearSparsityFraction`
- `jaxSupportSparsityFraction`

The JAX implementations use native array operations: `vmap`, `lax.scan`, `lax.associative_scan`, `jnp.lexsort`, ordered sparse-support prefix work, fixed-k `lax.top_k`, fused L1 reductions, and exact int64 arithmetic.

The Agda proof is for the finite computational law and its relation to the canonical definitions. It does not claim to prove the Python runtime or JAX compiler.

## Mirth proof-search synchronization

The import synchronizer treats the learner common-import block as canonical and checks exact byte equality with the theorem block.

Its independent predicates are:

- common-block marker counts;
- exact common-block equality;
- cross-monolith import direction;
- external SMT/Z3/Vehicle import counts.

These checks run concurrently. Write mode is protected by an atomic directory lock and bounded retry so concurrent writers cannot interleave the theorem rewrite.

The Mirth declaration graph generator separately reads both Agda monoliths and emits a deterministic Elm declaration graph.

## Dynamic declaration graph

The graph generator is intentionally distinct from the Mercury A* semantic frontier.

The generated graph contains:

- one node for every extracted top-level declaration;
- source tags for learner/theorem provenance;
- directed declaration-reference edges from declaration bodies;
- deterministic ordering;
- duplicate-edge elimination.

It is a source-derived relation graph, not a substitute for Agda elaboration.

The Pages application consumes this generated graph and exposes search, source filtering, incoming relations, outgoing relations, and a pure-Elm SVG neighborhood view.

## Interactive launcher

The interactive theorem path remains:

`bash tools/agda-auto-session.sh FullCoupled/TheoremsMonolith.agda`

The canonical batch Agda check remains authoritative after interactive proof search.

## Toolchain boundary

The non-JAX CI and development tooling does not carry a Python runtime. Python is isolated to the dedicated JAX workflow because JAX itself is a Python package.

Agda remains pinned at 2.8.0 and agda-stdlib at 2.3.

