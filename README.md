# Actions

Actions is a mechanically checked Agda system centered on one canonical recurrent learner. Agda proof terms are the semantic authority. Mercury, Dhall, Mirth, Nix, SMT, Vehicle, JAX, and Elm are supporting layers for dependency analysis, CI contracts, synchronization, execution, automation, or presentation.

## Authority and active tree

Exactly two Agda source files are tracked:

- `FullCoupled/CanonicalLearnerMonolith.agda`
- `FullCoupled/TheoremsMonolith.agda`

The learner monolith is the executable/type-level source of the canonical learner. The theorem monolith is the only derived-semantic consumer and imports the learner in one direction only.

The active Agda tree contains no `Exotic` namespace. The remaining namespace-only directory is `.github`, which is a platform convention.

Agda proof terms are authoritative. A graph edge, e-graph equivalence, solver result, generated Elm file, JAX execution result, or UI statement does not become a theorem without an accepted Agda term.

## Canonical learner

The learner monolith defines the concrete state and transition surface:

- GRU state and `gruStep`
- persistent matrix/noise/control tail and `persistentGRU`
- Watkins critic and trace state
- LCB counts and bonuses
- F4/L2 optimizer state
- q-log/control state
- sparsemax score ordering and support search
- `sparsemaxWeight`, `selectPositive`, and `sparsemaxPolicy`
- `canonicalFullStep` and `iterateCanonical`
- integer LayerNorm numerators and radicand
- recurrent/token and linear-Haar structures

The persistent GRU tail is structural rather than empirical: the learner proves one-step preservation and the theorem surface carries that fact through full-learner iteration.

## GRU left inverse, injectivity, convergence, and identifiability

The canonical statistical observation stores the original `GRUState`. Decoding by first projection gives a definitional left inverse.

The accepted proof chain is:

`canonicalGRUStatisticalDecodeEncode`

then

`canonicalGRUStatisticalEncodeLeftInverse`

then the general implication

`leftInverse-implies-injective`

then the concrete theorem

`canonicalGRUStatisticalEncodeInjective`.

The packaged theorem is `CanonicalGRUStatisticalInjectivityTheorem`.

This proves injectivity of the observation encoding. It does not prove that the recurrent transition `gruStep` is injective.

The reusable `GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem` consumes three explicit premises: an injective encoding, exact state/feature step conjugacy, and an eventually fixed feature tail. It derives tail-fixed source state, eventual stationarity, and identifiability. It does not manufacture physics, economics, or Baird witnesses.

## Hidden-Synergy L1, 1-path norm, and sparsity surface

The repository now retains a dedicated finite formal surface for the hidden-synergy material instead of leaving the historical definitions only in Git history.

The paper behind the hidden-synergy request is Aditya Biswas, “Hidden Synergy: L1 Weight Normalization and 1-Path-Norm Regularization.” Its near-sparsity discussion is Shannon-entropy based; Tsallis-2 is therefore kept here as a separate exact formal extension rather than being relabeled as the paper's original near-sparsity definition. The paper centers L1 weight normalization and 1-path-norm regularization as the regularization structure.

The active theorem surface restores:

- `rowL1`
- `weightL1`
- `onePathVector`
- `onePathNorm`
- `rowL1OnesAbs`
- `onePathOneLayer`
- `HiddenSynergyNormPair`
- `layerNormPair`
- `hiddenSynergy-one-layer-exact`

The canonical hard/soft sparsity degeneration is retained and packaged as `CanonicalHardSparsityDegeneracyTheorem`. It is the exact zero-threshold equivalence between:

`HardSparse K s`

and

`SoftSparseBounded K s zero`.

The generalized finite Tsallis-2 extension is also explicit:

- `ActionWeights`
- `actionSupportCount`
- `actionWeightSum`
- `actionWeightSquareSum`
- `generalTsallis2Denominator`
- `generalTsallis2Numerator`
- `generalTsallis2NearSparsity`
- `generalTsallis2NearSparsity-zero`
- `generalTsallis2NearSparsity-definition`
- `generalSupportSparsity`
- `UniformSupportTsallisBoundary`

For a finite nonnegative weight family with total mass S, squared mass Q, and dimension d, the exact finite extension records the rational quantity `(d Q - S²) / (d Q)`, with an explicit zero-vector convention. The uniform-support record isolates the equality condition needed to connect weighted effective support to hard support cardinality.

The finite Agda layer is exact. Continuous entropy, Lipschitz, differentiability, and convexity claims remain separate proof obligations rather than being inferred from those finite equalities. citeturn219666academia0

## Canonical-learner Baird boundary

No generic arbitrary-state, arbitrary-weight, or arbitrary-update Baird theorem remains in the active proof surface.

The surviving construction is:

`CanonicalLearnerBairdSevenStarBoundary K s`

with the concrete canonical learner kernel and state as parameters.

Its record fixes the seven-state/eight-feature setup, behavior probabilities 6/7 and 1/7, solid target behavior, zero reward, 99/100 discount, the upper-state representation `2 * wᵢ + w₈`, the lower-state representation `w₇ + 2 * w₈`, the already-proved persistent-GRU iterate tail, and an explicit divergence witness.

The divergence statement is supplied at this concrete learner boundary. Generic Baird records were pruned rather than being reused as a false universal theorem.

## Physics and economics

Physics and economics remain present.

The theorem monolith still includes Hodge-Maxwell and four-law semantic interfaces, GRU/physics transport, production structures, individual and aggregate demand/supply, excess-demand constructions, supporting-price and market-clearing witnesses, Walrasian interfaces, stationary and fixed-point closures, and economic composition.

Redundant thin wrapper endpoints were pruned where stronger closures already carried the semantic payload. The underlying physics and economics definitions were not deleted.

The GRU injectivity, convergence, or identifiability kernel does not create those domain correspondences. Exact transport and interpretation conditions remain explicit Agda premises.

## PPAD boundary

The repository does not claim PPAD-completeness.

Fixed-point and equilibrium constructions are present, but a PPAD-completeness theorem requires a concrete total polynomial-size search relation, an explicit polynomial encoding bound, membership in PPAD, and a hardness reduction. Those proof objects are not currently promoted as theorem authority.

## Data-structure choices

`List` is appropriate where the object is actually a finite ordered sequence: score entries, token sequences, candidate traces, plans, and similar data.

`Monoid` expresses algebraic structure and laws over a carrier, such as append associativity and identities. It does not replace the concrete carrier.

`Set` is the proposition/predicate/relations layer used throughout the Agda theorem surface.

`Monad` is used at operational effect/state boundaries, such as stateful A* surfaces. It is not a substitute for the underlying list or theorem carrier.

A finite-map or `Dict` layer is not currently justified by a proof obligation. A vector or `Fin`-indexed carrier becomes useful when the sequence length itself must be proof-relevant.

## JAX execution mirror

`tools/jax_reference.py` is the only Python execution boundary.

Its import surface is JAX itself:

`jax`

`jax.numpy`

`jax.lax`

No separate NumPy, SciPy, Flax, Optax, or other ML framework is imported.

The current executable JAX kernels are:

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

The array algorithms use native JAX execution where that reduces redundant traversal: `vmap` for independent maps, `lax.associative_scan` for associative prefixes, `lax.scan` for recurrence and the 1-path matrix chain, `jnp.lexsort` for deterministic order, one ordered prefix pass for sparse support, `lax.top_k` only for fixed-k specialization, fused reduction for L1 quantities, and exact JAX `int64` arithmetic for the integer kernels.

The theorem monolith mirrors every one of these current JAX functions with named Agda counterparts in `JAXExecutionMirrorReproof`, including the newly restored L1, 1-path, Tsallis-2, and support-sparsity kernels.

The Agda layer proves the finite computational laws and exact relations to the canonical definitions. It does not claim to prove the Python interpreter, the JAX compiler, `jit`, or shape-tracing implementation itself.

The dedicated JAX workflow is the only place where a Python runtime is required. The Nix development shell, Dhall CI helpers, shell helpers, and Mirth programs contain no Python runtime or Python package dependency. CI explicitly guards this separation.

## Mercury graph and Mirth graph

Mercury contains the semantic dependency/A* graph and e-graph analysis. Its required theorem registry is reconciled against the active Agda theorem monolith; stale historical Tsallis/Hodge/Walrasian requirement names are not kept as active theorem targets.

The Mercury review frontier remains a curated semantic frontier. It is not the same artifact as the exhaustive declaration relation graph.

The exhaustive declaration graph is generated by `.ci/mirth/agda_graph.mth`. That generator reads both active Agda monoliths, extracts top-level declarations, scans declaration bodies for references to known declarations, builds source-tagged directed edges, deduplicates and sorts the result, and emits a generated Elm module named `GeneratedAgdaGraph`.

The graph is generated concurrently at the source-extraction and edge-extraction stages. It is deterministic after sorting and duplicate elimination. It is a declaration-reference graph, not an Agda elaborator; accepted Agda proof terms remain the authority.

## Mirth synchronization and concurrency

`.ci/mirth/agda_import_sync.mth` treats the learner common-import block as the source of truth.

It checks:

- exactly one begin marker and one end marker in each monolith;
- byte-identical common import blocks;
- no learner-to-theorem back-edge;
- exactly one canonical learner import in the theorem monolith;
- exact Schmitty, Z3 backend, and Vehicle import counts.

Its independent predicates run concurrently under `wait`, with failure aggregation. Its write mode uses an atomic directory lock with bounded retry, so two writers cannot rewrite the theorem import block simultaneously.

The ASCII and graph Mirth programs follow the same compile-then-execute pattern. Their C99 executables are never treated as proof authority.

## Pure Elm GitHub Pages presentation

The Pages application remains pure Elm.

`site/Main.elm` is presentation-only. It does not execute Agda, JAX, Mirth, Mercury, or solver code at runtime.

The Pages workflow first generates `GeneratedAgdaGraph.elm` from the two Agda monoliths through Mirth/C99, then compiles the Elm program against that generated graph data.

The presentation supports:

- declaration-name search;
- learner/theorem source filtering;
- selected-node inspection;
- complete incoming and outgoing recorded relations for the selected declaration;
- an SVG neighborhood graph;
- counts of declarations and relations;
- direct source navigation within the Elm application.

No Mermaid runtime dependency is required.

The graph therefore behaves like a Mermaid-style interactive relation view while keeping the executable page pure Elm and the graph data generated directly from the current Agda source.

## Repository contracts

The verification surface enforces:

- exactly two tracked Agda files;
- Agda 2.8.0 and standard library 2.3;
- exact learner-to-theorem import direction;
- Mirth import synchronization and concurrency checks;
- generated Agda declaration graph generation;
- Mercury purity and theorem-registry reconciliation;
- physics/economics semantic surfaces;
- canonical-learner-only Baird boundary;
- GRU left-inverse and injectivity theorem surface;
- JAX-only Python execution boundary;
- JAX execution and shape checks;
- link-free Markdown outside the Elm application;
- absence of stale `Exotic` source paths;
- pure Elm Pages compilation;
- pinned Nix composition.

## Documentation

The Markdown surface is deliberately link-free. Navigation belongs in the Elm presentation.

Tracked detailed documents:

- `docs/agda-auto-proof-search.md`
- `docs/agda-smt-vehicle-boundary-2026-09-30.md`

The proof-search document covers theorem authority, left-inverse/injectivity construction, Baird specialization, the L1/1-path/Tsallis formal boundary, and the JAX/Agda execution mirror.

The SMT/Vehicle document covers external automation boundaries, import synchronization, Mirth concurrency, graph generation, Python/JAX isolation, Baird specialization, physics/economics status, and the PPAD boundary.

## Research-status discipline

A repository-level theorem is established by its accepted Agda proof term. Mercury graph discovery, e-graph saturation, JAX execution, or an Elm visualization can reveal relations and validate implementations, but they cannot independently promote a conjectured edge to theorem status.

The new GRU injectivity/conjugacy/tail-stability composition is therefore recorded as a formal repository result. It is not described as scholarly novelty without an independent literature comparison.
