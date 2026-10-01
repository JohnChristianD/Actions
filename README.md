# Actions

Actions is a mechanically checked Agda system centered on one canonical recurrent learner. Agda proof terms are the semantic authority; Mercury, Dhall, Mirth, Nix, SMT, Vehicle, JAX algorithm contracts, and Elm are supporting layers.

## Authority

Exactly two Agda sources are active:

- `FullCoupled/CanonicalLearnerMonolith.agda`
- `FullCoupled/TheoremsMonolith.agda`

The learner is the source definition. The theorem monolith is its one-way derived-semantic consumer. There is no active `Exotic` namespace.

## Canonical learner and GRU proof chain

The learner defines the concrete recurrent state, `gruStep`, persistent GRU channels, Watkins/critic state, LCB state, F4/L2 optimizer state, q-log/control state, sparsemax policy selection, `canonicalFullStep`, canonical iteration, integer LayerNorm arithmetic, token/recurrent structures, and linear-Haar structures.

The canonical statistical observation stores the original `GRUState), and its decoder is first projection. The accepted left-inverse chain is:

`canonicalGRUStatisticalDecodeEncode` → `canonicalGRUStatisticalEncodeLeftInverse` → `leftInverse-implies-injective` → `canonicalGRUStatisticalEncodeInjective`.

The packaged result is `CanonicalGRUStatisticalInjectivityTheorem`. This is injectivity of the observation encoding, not an unsupported claim that `gruStep` itself is injective.

`GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem` then composes an injective encoding, exact state/feature step conjugacy, and an eventually fixed feature tail to derive tail-fixed source state, eventual stationarity, and identifiability.

## Canonical-learner Baird boundary

There is no generic Baird theorem or generic Baird record.

`CanonicalLearnerBairdSevenStarWitness K s` is tied directly to the supplied canonical learner kernel/state. Its tail field uses the already-proved `canonicalPersistentGRU-afterFullStep-iterate K n s` result for that same learner. The witness carries the seven-state/eight-feature construction, 6/7 versus 1/7 behavior, solid target, zero reward, 99/100 discount, upper/lower feature equations, and an explicit divergence witness.

Thus Baird is a boundary witness for the already-tail-stable canonical learner, not a generic off-policy approximation template.

## Hidden-Synergy sparsity surface

The L1 and 1-path-norm material has been pruned from the active theorem surface because those functions and wrappers were not required by the canonical proof obligations.

The following remain:

- `CanonicalHardSparsityDegeneracyTheorem`, proving the exact zero-threshold hard/soft sparse equivalence;
- finite Tsallis-2 definitions `ActionWeights`, `actionSupportCount`, `actionWeightSum`, `actionWeightSquareSum`;
- `generalTsallis2Denominator`, `generalTsallis2Numerator`, `generalTsallis2NearSparsity`;
- `generalTsallis2NearSparsity-zero` and `generalTsallis2NearSparsity-definition`;
- `generalSupportSparsity` and `generalSupportSparsity-definition`;
- `UniformSupportTsallisBoundary`.

These are finite constructive definitions/equalities. They do not assert continuous Shannon, Lipschitz, differentiability, convexity, or analytic results that have not been formalized.

## Physics, economics, and PPAD

Physics and economics remain active. The theorem monolith retains Hodge-Maxwell/four-law interfaces, GRU/physics transport, production, demand/supply, excess demand, market-clearing and supporting-price witnesses, Walrasian interfaces, stationary/fixed-point closures, and economic composition.

The PPAD boundary remains explicit: no PPAD-completeness theorem is claimed. A genuine completeness proof still needs a total polynomial-size search relation, encoding-size bounds, membership, and a concrete hardness reduction.

## JAX algorithm contracts

The Python JAX wrapper and its workflow are not part of the repository anymore. The retained JAX-facing surface is the typed Agda contract in `JAXExecutionMirrorReproof`.

The retained algorithm contracts are vectorized affine mapping, associative prefix execution, recurrent scan, lexicographic score ordering, sparse-support size/top-k/policy selection, integer LayerNorm centered numerators and radicand, batched radicand, signed gating, scalar and batched GRU hidden updates, finite Tsallis-2 near-sparsity, support sparsity, and scan-sum.

Every retained contract has an Agda definition and equality law. The prefix and batched-GRU fields are checked against their actual finite Agda counterparts rather than tautological self-equalities. This proves the finite algorithm contracts, not a Python interpreter or JAX compiler.

## Data structures

`List` is used for concrete finite ordered sequences such as traces, token sequences, score lists, and candidate plans.

`Monoid` supplies algebraic laws over a carrier and is not a replacement for the carrier. `Set` supplies proposition/predicate/relation types. `Monad` is reserved for effect/state boundaries. A finite-map or Dict layer is not currently justified; vectors or `Fin`-indexed carriers become relevant only when sequence length itself must be proof-relevant.

## Mercury and source graphs

Mercury remains the semantic-analysis layer for theorem dependency, A*, and e-graph reasoning. Its semantic frontier is distinct from the exhaustive source-reference graph.

The Mirth Agda graph reads both monoliths, extracts top-level declarations and source-level identifier references, deduplicates and sorts edges, and emits the complete generated relation dataset consumed by Elm. The graph is source-derived rather than an Agda elaborator, so accepted Agda proof terms remain authoritative.

The Elm page exposes the generated nodes and all generated edges with declaration search, learner/theorem filtering, selected-node detail, complete incoming/outgoing relations, relation counts, and a dynamic SVG neighborhood. This is Mermaid-like interaction without a Mermaid runtime dependency.

## Mirth synchronization

The Mirth import synchronizer treats the learner common-import block as the source of truth. It checks marker cardinality, byte-identical common imports, learner-to-theorem-only dependency direction, canonical learner import count, and exact external SMT/Z3/Vehicle import counts.

The predicates execute concurrently and aggregate failures. Write mode is lock-protected and constructs the complete replacement before swapping it into the theorem monolith. The ASCII, import, and graph Mirth programs are compile-then-execute integration checks, not proof authorities.

## Repository constraints

CI enforces exactly two tracked Agda sources, Agda 2.8.0 with standard library 2.3, synchronized imports, canonical-learner-only Baird, retained physics/economics surfaces, GRU left-inverse/injectivity, the retained JAX algorithm contracts, link-free Markdown, absence of stale `Exotic` paths, pure Elm compilation, and pinned Nix composition.

No Python source files or shell-script files are part of the active repository surface.

## Documentation

The detailed Markdown documents cover proof authority, the canonical Baird boundary, the retained Tsallis-2/hard-sparsity surface, the PPAD boundary, the JAX/Agda contract layer, Mirth synchronization, Mercury/source graphs, and the pure Elm presentation.

Tracked Markdown contains no external links.
