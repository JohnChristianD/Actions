# Actions

Actions is a mechanically checked Agda system for one canonical recurrent learner and the theorem, search, execution, and presentation layers built around that learner. The repository deliberately separates proof authority from automation and execution: Agda proves the semantic statements; Mercury, Dhall, Mirth, Nix, Elm, SMT, Vehicle, and JAX support verification, discovery, orchestration, or presentation without silently becoming proof authority.

## Exact repository authority

There are exactly two tracked Agda authority files:

- `FullCoupled/CanonicalLearnerMonolith.agda`
- `FullCoupled/TheoremsMonolith.agda`

The learner monolith defines the concrete state and transition functions. The theorem monolith is the only derived-semantic consumer of that learner and imports it in one direction only.

The active Agda tree has no `Exotic` namespace. The only directory retained without an application child namespace is `.github`, which is a platform convention.

The authority order is Agda proof terms first, then Mercury theorem/dependency analysis, Dhall CI contracts, pinned toolchain composition, Mirth synchronization, and finally pure Elm presentation. Generated output, graph edges, solver suggestions, numerical execution, and UI text do not become theorems merely because they passed a supporting check.

## Canonical learner surface

The learner monolith contains the concrete `FullLearnerState`, `GRUState`, optimizer state, count state, Q-log/control state, sparse policy readout, recurrent transition, and full learner transition `canonicalFullStep`.

Important executable definitions include `gruStep`, `persistentGRU`, `integerLayerNormCenteredNumerators`, `integerLayerNormRadicand`, `scoreList`, `sortScores`, `topCodes`, `searchSupport`, `supportSize`, `sparsemaxWeight`, `selectPositive`, `sparsemaxPolicy`, `canonicalFullStep`, and `iterateCanonical`.

The persistent GRU tail is structural: `persistent-preservation` proves that the matrix/noise/control channels are unchanged by each GRU step, and the iterate-level theorem carries that persistence through the concrete full learner.

The count component is explicit and advances with the learner. The canonical full step therefore has a real state transition rather than an implicit mathematical placeholder.

## GRU left inverse, injectivity, convergence, and identifiability

The canonical statistical observation explicitly contains the original `GRUState`. The decoder is the first projection.

The proof chain is concrete and accepted by Agda:

`canonicalGRUStatisticalDecodeEncode` proves the left inverse definitionally;

`canonicalGRUStatisticalEncodeLeftInverse` exposes that fact as the named left-inverse theorem;

`leftInverse-implies-injective` proves the general implication from a left inverse to injectivity;

`canonicalGRUStatisticalEncodeInjective` instantiates that implication for the canonical GRU statistical encoding;

`CanonicalGRUStatisticalInjectivityTheorem` packages the encoding, decoder, left inverse, and injectivity into one theorem record.

This is encoding injectivity. It is not a claim that the recurrent transition `gruStep` is injective.

The reusable `GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem` is separate. It requires three explicit premises: injective encoding, exact state/feature step conjugacy, and an eventually fixed feature tail. From those premises it derives a tail-fixed source state, eventual stationarity, and identifiability. The theorem is a reusable kernel; it does not invent physical or economic interpretation.

## Canonical-learner Baird boundary

No generic arbitrary-state, arbitrary-weight, or arbitrary-update Baird theorem remains.

The surviving declaration is `CanonicalLearnerBairdSevenStarBoundary K s`. It is indexed by the actual `CanonicalFullLearnerKernel` and actual `CanonicalFullLearnerState`. Its fields fix the seven-state/eight-feature construction, 6/7 versus 1/7 behavior split, solid target policy, zero reward, 99/100 discount factor, and the upper/lower feature equations. It also carries the already-proved persistent-GRU tail invariant for `iterateCanonical`.

Its divergence conclusion is an explicit witness field:

`divergenceWitness` states that no globally eventually fixed canonical-full-learner state is supplied by that witness.

This is therefore a Baird boundary for the already-defined learner, not a generic Baird package.

## Physics and economics remain explicit

Physics and economics were not removed.

The theorem monolith still contains the Hodge-Maxwell and four-law semantic interfaces, GRU/physics transport, production structures, demand and supply structures, aggregate excess-demand kernels, supporting-price and market-clearing witnesses, Walrasian interfaces, stationary/fixed-point closures, and economic composition results.

Earlier redundant wrapper endpoints were pruned where the stronger closure already contained the same semantic payload. The retained economic closures now use the actual stationary, equilibrium, representation, and e-graph premises instead of duplicating thin wrapper theorems.

No physics or economic correspondence is inferred merely from the generic GRU convergence or injectivity kernel. The relevant semantic bridges remain explicit Agda premises and proofs.

## PPAD-completeness boundary

The repository does not claim a PPAD-completeness theorem.

The current proof surface contains fixed-point and equilibrium machinery, but fixed-point vocabulary alone is not a PPAD result. A genuine PPAD-completeness proof would need a concrete polynomial-size search relation, totality, membership in PPAD, explicit polynomial encoding/size bounds, and a reduction establishing hardness. Those proof objects are not present, so no PPAD-completeness label is promoted.

This is an explicit proof boundary, not an omitted implementation detail.

## List, Monoid, Monad, Set, and finite maps

The concrete learner uses `List` where the object is actually a finite ordered sequence: score entries, token sequences, candidate traces, plans, and similar finite data.

`Monoid` is used for algebraic laws such as append associativity and identities. It describes structure on a carrier; it does not replace a concrete list carrier.

`Set` is Agda's proposition-level universe for predicates, relations, and theorem statements. It is foundational to the proof surface rather than a sequence container.

`Monad` is used at effect/state boundaries, such as the operational A* search surface. It is not used as a substitute for the underlying list or theorem carrier.

A finite-map/`Dict` layer is not currently justified by a theorem requirement. Adding one would introduce lookup and finite-key machinery without improving an existing proof boundary. A vector or `Fin`-indexed carrier becomes useful only when sequence length itself must be proof-relevant.

## JAX execution mirror and Agda reproof surface

`tools/jax_reference.py` is a JAX-only execution mirror. Its third-party runtime surface is JAX itself: `jax`, `jax.numpy`, and `jax.lax`. It does not import NumPy as a separate package, Flax, Optax, SciPy, or another ML framework.

The mirror covers every current JAX function:

- `vmap_affine`
- `associative_prefix_sum`
- `recurrent_scan`
- `lexicographic_score_order`
- `sparse_support_size`
- `sparse_support_top_k`
- `sparsemax_policy_index`
- `integer_layernorm_centered_numerators`
- `integer_layernorm_radicand`
- `batched_integer_layernorm_radicand`
- `signed_gate`
- `gru_hidden_step`
- `batched_gru_hidden_step`
- `jitted_scan_sum`

The JAX algorithms prefer array-native execution where it is materially better: `vmap` for independent maps, `lax.scan` for recurrent state, `lax.associative_scan` for associative prefixes, `jnp.lexsort` for deterministic score ordering, one sorted prefix pass for sparse support, `lax.top_k` only for fixed-`k` specialization, and exact `int64` arithmetic for the integer kernels.

The JAX execution lane is separate from the Nix/Dhall/Mirth toolchain. Python is not included in the Nix development shell and is not used by the Mirth, Agda integration-sync, ASCII, or README shell helpers. The dedicated JAX workflow supplies the Python runtime required by JAX and installs the single pinned JAX package for that lane.

The theorem monolith contains a typed Agda counterpart/reproof surface for all of those computational functions, collected in `JAXExecutionMirrorReproof`. The Agda surface proves the corresponding finite computational laws and exact equivalences to the canonical learner definitions. It does not pretend to prove the behavior of the Python interpreter, JAX's compiler, `jit`, or shape tracer by reflection.

## Mirth, C99, Nix, and Elm

Mirth sources are used for fast-dirty generation and synchronization:

- `.ci/mirth/agda_to_elm.mth`
- `.ci/mirth/ascii_surface.mth`
- `.ci/mirth/agda_import_sync.mth`

The Agda import synchronizer uses the learner's common import block as the source of truth. It checks exact block equality, checks the single learner-to-theorem cross-monolith import, and checks the external SMT/Z3/Vehicle import counts.

Mirth compiles its source to C99 for these checks. Nix supplies the pinned compiler/toolchain environment; it is not a replacement for C99 and is not described as one.

The Pages application is pure Elm. `site/Main.elm` contains presentation only: it does not define learner semantics, theorem proofs, or a runtime dependency on Mermaid.

## CI and verification contracts

The repository contracts cover:

- exactly two tracked Agda monoliths;
- canonical learner safety checking;
- theorem checking with the external SMT and Vehicle interfaces;
- exact learner-to-theorem import direction;
- GRU statistical left-inverse and injectivity theorem names;
- the canonical-learner-specific Baird boundary;
- physics/economics theorem surfaces and explicit semantic bridges;
- Mercury purity and theorem-registry checks;
- Mirth import synchronization and ASCII synchronization;
- link-free Markdown outside the Elm presentation;
- flattened Agda paths and the absence of stale `Exotic` source paths;
- pure Elm compilation and Pages verification;
- JAX execution-mirror compilation and shape checking;
- pinned Nix composition.

## Documentation

The public Markdown surface is intentionally link-free. Navigation links are kept inside the Elm presentation where they belong.

Tracked detailed documents:

- `docs/agda-auto-proof-search.md`
- `docs/agda-smt-vehicle-boundary-2026-09-30.md`

The proof-search document records the concrete left-inverse/injectivity workflow, the canonical Baird boundary, and the JAX/Agda execution boundary.

The SMT/Vehicle document records the external automation boundary, import synchronization, canonical tail stability, the canonical Baird proof boundary, PPAD non-claim, physics/economics status, and the JAX mirror/reproof architecture.

## Research-status discipline

The repository can establish repository-level theorems and exact implementation equivalences through accepted Agda proof terms. Graph interlinks may reveal useful composition paths. Neither graph discovery nor the existence of a new composition theorem by itself establishes scholarly novelty.

The GRU injectivity/conjugacy/tail-stability composition is therefore documented as a formal repository result and semantic interlink. A literature-backed novelty claim would require an independent comparison against prior work.

<!-- BEGIN RECENT COMMIT TOTALITY -->
last-processed-commit: a8c95922dcde4c2e8d09e61e3215d24fc5ce1237
unprocessed-commit-count: 0

The scheduled updater accounts for every commit since the previous processed commit.
ascii-safe-commit-subjects: true
<!-- END RECENT COMMIT TOTALITY -->

<!-- BEGIN GENERATED DOCUMENTATION INDEX -->

Generated from the tracked Markdown surface: 2 files.
The root README is the GitHub-facing entry point; detailed evidence remains in the tracked source documents. Internal CI/discovery notes and historical agent plans are intentionally excluded from this public documentation index.

### Repository documentation

- `docs/agda-auto-proof-search.md` — Agda proof search in this repository
- `docs/agda-smt-vehicle-boundary-2026-09-30.md` — Agda SMT automation and Vehicle boundary — 2026-09-30

<!-- END GENERATED DOCUMENTATION INDEX -->
