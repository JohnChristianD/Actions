# Actions

This repository is a mechanically checked Agda system for a canonical recurrent learner, its exact state transitions, algebraic/proof kernels, and explicit physics/economics/game-theory boundaries. The public presentation is pure Elm; CI orchestration is split among GitHub Actions, Dhall, Nix, Mirth/C99, and Mercury.

## Authority and repository shape

The proof authority is exactly two tracked Agda monoliths:

- `FullCoupled/CanonicalLearnerMonolith.agda`
- `FullCoupled/TheoremsMonolith.agda`

The first file owns concrete learner definitions and definitional laws. The second owns derived propositions and their proofs. The theorem monolith imports the learner in one direction only.

There is no active `Exotic` namespace. The only namespace-only directory retained for convention is `.github`.

The authority order is:

1. Agda source and accepted proof terms.
2. Mercury theorem extraction, dependency graphs, and equality saturation.
3. Dhall CI contracts.
4. Nix environment composition and pinned inputs.
5. Mirth/C99 synchronization checks.
6. Pure Elm presentation.

Generated graphs, solver output, model weights, reports, and UI artifacts are never promoted to proof authority merely because CI can consume them.

## Canonical learner

The learner monolith defines the concrete full learner state, including GRU state, Watkins/Learning-Count-Balance state, optimizer state, count state, and Q-log/control state. It defines `canonicalFullStep` and `iterateCanonical`.

Important facts already present in the proof surface include:

- GRU matrix/noise/control persistence is preserved by every GRU step;
- the same persistent GRU tail is preserved across every iterate of the full canonical learner;
- the canonical total count advances by one per learner step;
- the canonical full step has no one-step fixed point;
- token sequences are concrete finite `List` values;
- `Monoid` supplies algebraic laws for operations rather than replacing sequence carriers;
- `Monad` is reserved for effect/state boundaries;
- a finite-map/`Dict` layer is not added without a theorem-level requirement.

## GRU injectivity and left inverse

The canonical statistical encoding explicitly contains the original `GRUState`, while its decoder returns that embedded state. The repository now proves the left inverse

`canonicalGRUStatisticalDecode (canonicalGRUStatisticalEncode s) ≡ s`

and derives

`canonicalGRUStatisticalEncodeInjective`

through the generic proved implication `leftInverse-implies-injective`.

This is an encoding theorem. It is not a claim that `gruStep` itself is injective. The transition is only called injective when its concrete definition supplies the required proof.

The reusable convergence kernel separately consumes injective encoding, exact step conjugacy, and an eventually fixed feature tail. Its outputs are tail-fixed source state, eventual stationarity, and identifiability.

## Canonical-learner Baird boundary

The former generic Baird records are removed.

The surviving declaration is `CanonicalLearnerBairdSevenStarBoundary`, indexed by an actual `CanonicalFullLearnerKernel` and an actual `CanonicalFullLearnerState`. It retains the seven-state/eight-feature construction, 6/7 versus 1/7 behavior split, solid target policy, zero reward, discount 0.99, and the upper/lower feature equations.

The package also carries the already-proved persistent-GRU tail invariant for that exact learner iteration. Its numerical divergence proposition remains an explicit witness field. No generic arbitrary-weight/arbitrary-update Baird theorem remains.

## Physics and economics

Physics and economics were not removed.

The theorem monolith still contains Hodge-Maxwell and four-law semantic interfaces, GRU/physics transport, production and demand/supply structures, aggregate excess-demand kernels, supporting-price and market-clearing witnesses, Walrasian interfaces, and stationary/fixed-point/economic closures.

The GRU convergence and injectivity layers do not manufacture those semantic correspondences. Their transport, fixed-point, equilibrium, and interpretation premises remain explicit.

The graph's new injectivity/conjugacy interlink is repository-level semantic composition, not a claim of scholarly novelty. Establishing novelty would require a literature comparison.

## PPAD and computability boundaries

No PPAD-completeness theorem is claimed.

A real PPAD-completeness result would require an explicit polynomial-time search relation, a totality proof, a membership proof, a PPAD-hardness reduction, and polynomial size bounds for the encoding. Those reductions are not present in the current Agda surface, so the repository does not infer a PPAD label from fixed-point terminology.

No blanket Turing-completeness or compression/prediction theorem is inferred from recursion or algebraic structure either.

## JAX execution mirror

`tools/jax_reference.py` provides a JAX-only execution mirror for the computational kernels where JAX has a clear array-execution advantage. The current mirror covers:

- independent maps with `jax.vmap`;
- fixed-length recurrent execution with `jax.lax.scan`;
- associative prefix work with `jax.lax.associative_scan`;
- score ordering with `jax.numpy.lexsort`;
- dynamic sparse-support discovery with one sorted prefix pass, plus a specialized fixed-`k` `jax.lax.top_k` path;
- exact integer LayerNorm radicands;
- the concrete GRU hidden-state update used by the learner.

The mirror uses JAX `int64` arithmetic so these kernels preserve the Agda `Int8` wrapper's unbounded-integer semantics rather than introducing floating-point approximation. The check runs `jax.jit` and `jax.eval_shape`; it adds no Flax, Optax, NumPy-side algorithm package, or other ML library.

JAX is an executable optimization/reference boundary, not a proof authority. Theorem records, injectivity, left-inverse proofs, convergence proofs, physics/economics bridges, and the canonical-learner Baird boundary remain Agda proofs. The theorem monolith has no computational algorithm that can be safely replaced by a JAX runtime without changing the proof architecture.

JAX is pinned to 0.11.2 in its dedicated verification workflow. Update the workflow and this section together when the pinned JAX release changes.

## Mirth and Elm

The tracked Mirth sources are:

- `.ci/mirth/agda_to_elm.mth`
- `.ci/mirth/ascii_surface.mth`
- `.ci/mirth/agda_import_sync.mth`

The import synchronizer takes the learner common-import block as the source of truth and checks that the theorem monolith has the byte-identical common block plus intentionally theorem-specific imports. The only cross-monolith import is the theorem monolith importing the canonical learner.

`site/Main.elm` is pure Elm and presentation-only. It exposes the proof topology, theorem boundaries, Baird boundary, PPAD/JAX status, data-structure decisions, and CI contracts. It defines no learner semantics and no proof evidence. Mermaid is not a runtime dependency.

## Toolchain and verification

The Agda workflows use the first-party Agda setup action with Agda 2.8.0 and agda-stdlib 2.3.

Schmitty is checked against its pinned Agda source and Z3 interface. Vehicle is checked at its pinned Agda interface boundary. Mercury performs theorem declaration discovery and equality-saturation checks. Nix pins the external source revisions and local toolchain.

The CI contract checks:

- exactly two canonical Agda monoliths;
- learner `--safe` checking;
- theorem checking with the explicit external integrations;
- exact learner-to-theorem import direction;
- the concrete GRU left-inverse and injectivity surface;
- the canonical-learner-specific Baird boundary;
- Mercury semantic extraction and graph closure;
- Mirth import and ASCII synchronization;
- flattened Agda source paths;
- pure Elm compilation and Pages verification;
- JAX execution-mirror compilation/shape verification with the JAX package only;
- pinned Nix composition.

## Documentation index

Generated from the tracked Markdown surface:

- `docs/agda-auto-proof-search.md` — Agda proof-search policy and concrete injectivity workflow.
- `docs/agda-smt-vehicle-boundary-2026-09-30.md` — SMT, Vehicle, GRU convergence, Baird, PPAD, and JAX boundaries.

The Markdown surface intentionally contains no external hyperlinks. The Elm presentation surface may contain navigational links to repository source.

## Maintenance rule

When a theorem appears to connect GRU dynamics with physics, economics, games, complexity, or external numerical behavior, its exact semantic bridge must appear as an Agda premise or proof. Graph discovery can suggest an edge; it cannot create the edge.

<!-- BEGIN RECENT COMMIT TOTALITY -->
last-processed-commit: bb17fff50722b2d82bf08e1bc53f1b171de4b5a4
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