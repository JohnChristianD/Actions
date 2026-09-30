# Agda SMT automation and Vehicle boundary — 2026-09-30

## Scope

The tracked Agda surface is exactly:

- `FullCoupled/CanonicalLearnerMonolith.agda`
- `FullCoupled/TheoremsMonolith.agda`

The learner is checked independently. The theorem monolith is the sole derived-semantic consumer of the canonical learner.

## Schmitty

The theorem monolith exposes a closed integer normalization fact through Schmitty and the Z3 backend. The external solver is an automation boundary, not a second proof authority: Agda checks the resulting theorem term.

The CI contract checks the pinned Schmitty Agda source, its library metadata, its compatible Agda version, and the Z3 executable before the theorem check.

## Vehicle

Vehicle is consumed at its pinned Agda reflection/interface boundary. The repository does not treat a standalone Vehicle compiler build as theorem authority and does not introduce a third tracked Agda source module.

## Mirth import synchronization

The two monoliths share one exact common import block. Mirth treats the learner block as the source of truth.

The theorem monolith may add theorem-specific imports for Schmitty, Vehicle, induction, arithmetic, algebraic tactics, effect/state, and list-effect support. The only cross-monolith import is:

`open import FullCoupled.CanonicalLearnerMonolith as C`

The learner does not import the theorem monolith.

The synchronizer is concurrency-safe: independent logical predicates run in parallel and their exit statuses are aggregated. The write path uses an atomic directory lock with bounded retry, so two writers cannot concurrently rewrite the theorem common-import block.

## Mirth graph generation

`.ci/mirth/agda_graph.mth` reads both active Agda monoliths and generates `GeneratedAgdaGraph.elm`.

The source pass extracts top-level declarations from both files. The reference pass scans declaration bodies for known declaration names and emits directed source-tagged edges. Node and edge output is sorted and duplicate edges are removed.

This graph is intentionally a declaration-reference artifact. It does not claim to implement Agda elaboration, type inference, or proof checking.

The graph is generated in the Pages workflow before Elm compilation, and the same generator is exercised by the Mirth fast-dirty CI lane.

## GRU left inverse and injectivity

The canonical statistical encoding explicitly contains the original `GRUState`, and its decoder returns that state by first projection.

The theorem surface proves the left inverse and derives injectivity:

`canonicalGRUStatisticalDecodeEncode`

then

`canonicalGRUStatisticalEncodeLeftInverse`

then

`leftInverse-implies-injective`

then

`canonicalGRUStatisticalEncodeInjective`.

This is an encoding theorem. It does not imply that `gruStep` is injective.

## Canonical tail stability and convergence kernel

The learner proves persistence of the GRU matrix/noise/control tail under one step. The theorem surface lifts this fact to every full-learner iterate.

`GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem` is a reusable composition theorem with explicit premises for injective observation, exact state/feature conjugacy, and eventual feature-tail fixation. It derives tail-fixed source state, eventual stationarity, and identifiability only from those premises.

## Canonical-learner Baird boundary

Generic Baird records are not active theorem surfaces.

The surviving declaration is `CanonicalLearnerBairdSevenStarBoundary K s`, indexed by the actual canonical learner kernel and state. It contains the concrete seven-state/eight-feature data, 6/7 and 1/7 behavior probabilities, solid target, zero reward, 99/100 discount factor, upper/lower feature equations, the already-proved persistent-GRU iterate tail, and an explicit divergence witness.

The witness is specific to that learner boundary. It is not derived from a generic Baird theorem.

## Hidden-Synergy L1, 1-path norm, and sparse degeneration

The theorem monolith retains exact finite forms of the hidden-synergy regularization structure:

`rowL1`, `weightL1`, `onePathVector`, `onePathNorm`, `rowL1OnesAbs`, `onePathOneLayer`, `HiddenSynergyNormPair`, `layerNormPair`, and `hiddenSynergy-one-layer-exact`.

The canonical hard-sparse/soft-sparse zero-threshold equivalence is packaged as `CanonicalHardSparsityDegeneracyTheorem`.

The paper-faithful near-sparsity concept is kept distinct from the repository's Tsallis-2 extension. The original paper discusses near-sparsity through Shannon entropy while also centering L1 weight normalization and 1-path-norm regularization. citeturn219666academia0

The exact finite Tsallis-2 extension contains:

`ActionWeights`, `actionSupportCount`, `actionWeightSum`, `actionWeightSquareSum`, `generalTsallis2Denominator`, `generalTsallis2Numerator`, `generalTsallis2NearSparsity`, `generalTsallis2NearSparsity-zero`, `generalTsallis2NearSparsity-definition`, `generalSupportSparsity`, and `UniformSupportTsallisBoundary`.

Continuous entropy/Lipschitz/analytic conclusions are kept outside this finite equality layer.

## Physics and economics

Physics and economics remain in the active theorem monolith.

The current surface includes Hodge-Maxwell/four-law semantic interfaces, GRU/physics transport, production, demand and supply, aggregate excess-demand structures, supporting-price and market-clearing witnesses, Walrasian interfaces, stationary/fixed-point closures, and economic composition.

Historical thin wrapper endpoints were pruned; the underlying domain surfaces remain. The generic GRU injectivity/convergence kernel does not create these semantic correspondences.

## PPAD boundary

No PPAD-completeness theorem is claimed.

A valid proof would need an explicit total polynomial-size search relation, encoding-size bounds, PPAD membership, and a concrete hardness reduction. Fixed-point or equilibrium constructs alone do not establish completeness.

## JAX execution and Agda reproof

`tools/jax_reference.py` is the isolated Python boundary. Its imports are only:

`jax`, `jax.numpy`, and `jax.lax`.

The current executable kernels are:

`vmap_affine`, `associative_prefix_sum`, `recurrent_scan`, `lexicographic_score_order`, `sparse_support_size`, `sparse_support_top_k`, `sparsemax_policy_index`, `l1_row`, `l1_matrix`, `one_path_norm`, `tsallis2_near_sparsity_fraction`, `support_sparsity_fraction`, `integer_layernorm_centered_numerators`, `integer_layernorm_radicand`, `batched_integer_layernorm_radicand`, `signed_gate`, `gru_hidden_step`, `batched_gru_hidden_step`, and `jitted_scan_sum`.

The theorem monolith provides named finite Agda mirrors for all current functions, packaged by `JAXExecutionMirrorReproof`.

The efficient kernels use native array operations where useful:

- `vmap` for independent transforms;
- `lax.associative_scan` for associative prefixes;
- `lax.scan` for stateful recurrences and the 1-path matrix chain;
- `jnp.lexsort` for deterministic score order;
- one ordered prefix pass for sparse support;
- `lax.top_k` only for fixed-k specialization;
- fused absolute-value reductions for L1 quantities;
- exact JAX int64 arithmetic.

The JAX workflow is the only workflow that needs Python. The Nix shell and non-JAX CI/Mirth helpers contain no Python runtime or Python package dependency. A CI surface check rejects Python toolchain references outside that dedicated boundary.

The Agda reproof proves finite function laws and equivalences to canonical definitions. It does not claim to model JAX's Python interpreter or compiler internals.

## Mercury graph status

Mercury performs semantic dependency/A* and e-graph analysis. Its theorem requirement registry is reconciled against the active Agda theorem monolith, so stale historical Tsallis/Hodge/Walrasian names are not promoted as current theorem targets.

The semantic review frontier remains curated. The exhaustive declaration/reference graph is a separate Mirth-generated source graph consumed by Elm.

## Elm Pages

The Pages program is pure Elm and has no Mermaid runtime dependency.

The Pages workflow generates the current Agda declaration graph before compiling `site/Main.elm`. Elm then presents:

- declaration search;
- learner/theorem filtering;
- selected-node detail;
- complete recorded incoming and outgoing relations for the selected declaration;
- an SVG neighborhood graph;
- declaration and relation counts.

Elm is therefore a presentation layer over generated source facts, not another proof system.

## Python and toolchain boundary

No Python is provided by the Nix development shell. No Python is invoked by Mirth, import synchronization, ASCII synchronization, graph generation, or the general Dhall CI orchestration.

The only Python execution is the dedicated JAX workflow, which installs the pinned JAX package and runs `tools/jax_reference.py`.

## Markdown contract

Tracked Markdown is link-free. Navigation and external source navigation are kept inside the Elm presentation.

The three public Markdown files are the root README plus the two detailed documents in `docs/`.
