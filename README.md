# Actions

Actions is a mechanically checked Agda system centered on one canonical recurrent learner. Agda proof terms are the semantic authority. Mercury, Dhall, Mirth, Nix, SMT, Vehicle, JAX, and Elm are supporting layers for analysis, orchestration, synchronization, execution, and presentation.

## Active authority tree

Exactly two Agda source files are tracked:

- `FullCoupled/CanonicalLearnerMonolith.agda`
- `FullCoupled/TheoremsMonolith.agda`

The learner monolith defines the executable and type-level learner surface. The theorem monolith is the sole derived-semantic consumer and imports the learner in one direction.

There is no active `Exotic` namespace. The only namespace-only directory retained by the repository contract is `.github`, because it is a platform convention.

Agda proof terms are authoritative. A declaration graph edge, Mercury e-graph equivalence, SMT result, Vehicle result, JAX execution result, generated Elm module, or UI statement is supporting evidence rather than a theorem.

## Canonical learner

The learner monolith contains the concrete recurrent learner definitions used by the theorem surface, including:

- GRU state and `gruStep`;
- persistent matrix/noise/control data and `persistentGRU`;
- Watkins critic and trace state;
- LCB counts and bonuses;
- F4/L2 optimizer state;
- q-log and control state;
- sparsemax score ordering, support search, weights, and selected policy;
- `canonicalFullStep` and `iterateCanonical`;
- integer LayerNorm numerators and radicand;
- recurrent/token and linear-Haar structures.

The persistent GRU tail is proved at the learner level and transported through full-learner iteration. It is not an empirical assumption.

## GRU left inverse, injectivity, and convergence

The canonical statistical observation explicitly contains the original `GRUState`. Its decoder is first projection, giving a definitional left inverse.

The accepted proof chain is:

`canonicalGRUStatisticalDecodeEncode` → `canonicalGRUStatisticalEncodeLeftInverse` → `leftInverse-implies-injective` → `canonicalGRUStatisticalEncodeInjective`.

The packaged result is `CanonicalGRUStatisticalInjectivityTheorem`.

This proves injectivity of the observation encoding. It does not silently promote that fact to injectivity of `gruStep`.

The reusable `GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem` consumes an injective encoding, exact state/feature conjugacy, and an eventually fixed feature tail. It derives tail-fixed source state, eventual stationarity, and identifiability from those premises.

## Canonical-learner Baird construction

The Baird surface is not a generic arbitrary-state or arbitrary-update theorem.

The active declaration is `CanonicalLearnerBairdSevenStarWitness K s`. It is tied to the canonical learner kernel and state supplied at the boundary, and its tail component is exactly the accepted `canonicalPersistentGRU-afterFullStep-iterate` theorem for that same learner.

The witness records the seven-state/eight-feature construction, 6/7 versus 1/7 behavior, solid target, zero reward, 99/100 discount, the upper representation `2 * wᵢ + w₈`, the lower representation `w₇ + 2 * w₈`, the persistent-GRU iterate tail, and the explicit divergence witness.

No generic Baird record is retained.

## Hidden-Synergy L1, 1-path norm, hard sparsity, and Tsallis-2

The finite formal surface for the L1/1-path-norm hidden-synergy material is retained in the theorem monolith.

The active definitions and exact theorem include:

- `rowL1`;
- `weightL1`;
- `onePathVector`;
- `onePathNorm`;
- `rowL1OnesAbs`;
- `onePathOneLayer`;
- `HiddenSynergyNormPair`;
- `layerNormPair`;
- `hiddenSynergy-one-layer-exact`.

The canonical hard/soft sparse degeneration is retained as `CanonicalHardSparsityDegeneracyTheorem`. Its zero-threshold content is the exact equivalence between `HardSparse K s` and `SoftSparseBounded K s zero`.

The finite Tsallis-2 extension is also retained. Its current theorem-facing definitions are:

- `ActionWeights`;
- `actionSupportCount`;
- `actionWeightSum`;
- `actionWeightSquareSum`;
- `generalTsallis2Denominator`;
- `generalTsallis2Numerator`;
- `generalTsallis2NearSparsity`;
- `generalTsallis2NearSparsity-zero`;
- `generalTsallis2NearSparsity-definition`;
- `generalSupportSparsity`;
- `UniformSupportTsallisBoundary`.

For finite nonnegative weights, the exact rational extension is represented by the numerator/denominator pair corresponding to ((dQ-S^2)/(dQ)), with an explicit zero-vector convention. The finite formalization does not silently turn continuous entropy, Lipschitz, differentiability, or convexity claims into Agda equalities.

## Physics and economics

Physics and economics remain active.

The theorem monolith still contains Hodge-Maxwell and four-law semantic interfaces, GRU/physics transport, production, demand and supply, aggregate excess-demand structures, supporting-price and market-clearing witnesses, Walrasian interfaces, stationary/fixed-point closures, and economic composition.

Earlier pruning removed redundant thin wrappers, not the underlying physics or economics structures.

The GRU injectivity/convergence kernel is not being used to manufacture those domain correspondences. Their transport and interpretation conditions remain explicit theorem data.

## PPAD-completeness boundary

No PPAD-completeness theorem is claimed.

The repository contains fixed-point and equilibrium constructions, but a genuine PPAD-completeness result would need an explicit polynomial-size total search relation, encoding-size bounds, a PPAD membership proof, and a concrete hardness reduction. Those obligations are not replaced by naming a fixed point, equilibrium, or convergence construction.

## Data-structure discipline

`List` remains appropriate when the object is a finite ordered sequence: score entries, token sequences, candidate traces, plans, and similar data.

`Monoid` describes algebraic structure and laws over a carrier, such as append associativity. It is not a replacement for the carrier.

`Set` is the proposition, predicate, and relation layer used throughout the Agda theorem types.

`Monad` belongs at operational effect/state boundaries. It is not a replacement for a concrete sequence or theorem carrier.

A finite-map or `Dict` layer is not justified by a current proof obligation. A vector or `Fin`-indexed carrier becomes relevant only when sequence length itself must be proof-relevant.

## JAX execution mirror

`tools/jax_reference.py` is the only Python execution boundary.

Its third-party import boundary is JAX itself: `jax`, `jax.numpy`, and `jax.lax`. No NumPy, SciPy, Flax, Optax, or other ML framework is imported.

The current kernels are:

- `vmap_affine`;
- `associative_prefix_sum`;
- `recurrent_scan`;
- `lexicographic_score_order`;
- `sparse_support_size`;
- `sparse_support_top_k`;
- `sparsemax_policy_index`;
- `l1_row`;
- `l1_matrix`;
- `one_path_norm`;
- `tsallis2_near_sparsity_fraction`;
- `support_sparsity_fraction`;
- `integer_layernorm_centered_numerators`;
- `integer_layernorm_radicand`;
- `batched_integer_layernorm_radicand`;
- `signed_gate`;
- `gru_hidden_step`;
- `batched_gru_hidden_step`;
- `jitted_scan_sum`.

The implementation uses JAX-native array algorithms where they provide a genuine execution advantage: `vmap` for independent maps, `lax.associative_scan` for associative prefixes, `lax.scan` for stateful recurrences and the 1-path chain, `jnp.lexsort` for deterministic ordering, one ordered prefix pass for sparse support, `lax.top_k` only for fixed-k specialization, fused L1 reductions, and exact int64 arithmetic for the integer kernels.

The theorem monolith contains an Agda counterpart and accepted finite law for every current JAX kernel through `JAXExecutionMirrorReproof`. The reproof surface is not a claim about the Python interpreter or JAX compiler internals.

The non-JAX Nix shell, Mirth programs, Dhall orchestration, and shell helpers do not install or execute Python packages. The dedicated JAX workflow is the only Python boundary.

## Mercury semantic graph

Mercury performs semantic dependency, A*, and e-graph analysis over theorem declarations and their recorded laws.

The theorem registry is reconciled against the active Agda monolith, so stale historical theorem names do not become current proof targets. The semantic review frontier remains a curated reasoning surface; it is distinct from the exhaustive source-reference graph.

## Exhaustive Agda relation graph

`.ci/mirth/agda_graph.mth` reads both active Agda monoliths.

The graph pass extracts every top-level declaration it can identify from the source form, records its learner/theorem provenance, scans the declaration body for identifiers matching declarations from the same two files, emits directed reference edges, removes duplicates, and sorts the result deterministically.

The graph is therefore source-derived and exhaustive with respect to the parser's top-level declaration/reference model. It is not presented as an Agda elaborator: accepted Agda terms remain the proof authority.

The Pages program consumes the complete generated node and edge dataset. The UI supports declaration search, source filtering, selected-node inspection, complete incoming/outgoing relation lists, and a dynamic SVG neighborhood.

## Mirth synchronization and concurrency

`.ci/mirth/agda_import_sync.mth` treats the learner common-import block as the source of truth.

Its predicates verify:

- exactly one common-import begin/end marker in each monolith;
- byte-identical common blocks;
- learner-to-theorem-only cross-monolith direction;
- exactly one canonical learner import in the theorem monolith;
- exact Schmitty, Z3 backend, and Vehicle import counts.

Independent predicates execute concurrently and their statuses are aggregated. Write mode uses an atomic directory lock with bounded retry and writes a completed candidate before replacing the theorem block. This prevents concurrent writers from interleaving partial imports.

The ASCII and graph Mirth surfaces follow the same compile-then-execute model. None of these generated scripts are proof authorities.

## Pure Elm Pages presentation

The Pages application is pure Elm.

`site/Main.elm` reads the generated graph as data. It does not execute Agda, JAX, Mirth, Mercury, SMT, or Vehicle at runtime.

The presentation exposes the entire generated relation dataset through:

- declaration search;
- learner/theorem filtering;
- selected declaration detail;
- complete incoming relation list;
- complete outgoing relation list;
- relation counts;
- a dynamic SVG neighborhood;
- direct source navigation inside the Elm page.

The graph is generated from the current Agda files before Elm compilation. No Mermaid runtime dependency is required.

## Repository contracts

The CI surface checks, among other contracts:

- exactly two tracked Agda files;
- Agda 2.8.0 and standard library 2.3;
- learner-to-theorem-only Agda dependency direction;
- synchronized common imports;
- concurrency-safe Mirth predicates;
- complete source-derived Agda graph generation;
- Mercury theorem registry and purity;
- canonical-learner-only Baird surface;
- physics/economics semantic surfaces;
- GRU left-inverse and injectivity proof chain;
- JAX-only Python execution boundary;
- execution and shape checks for all JAX kernels;
- link-free tracked Markdown;
- absence of stale `Exotic` source paths;
- pure Elm compilation;
- pinned Nix composition.

## Documentation discipline

Tracked Markdown is link-free. The public Markdown surface is the root README plus the two detailed documents in `docs/`.

The detailed documents describe proof authority, the canonical-learner Baird construction, the L1/1-path/Tsallis surface, the PPAD boundary, JAX/Agda reproof, Mirth synchronization, the Mercury graph, and the pure-Elm presentation without using Markdown links.

Research status is stated conservatively: a repository theorem is established by its accepted Agda proof term. Graph discovery and execution can expose relations or validate implementations, but they do not independently establish scholarly novelty.
