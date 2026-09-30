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

## JAX boundary

There is currently no JAX source tree or JAX dependency in this repository. The proof surface is Agda-native and does not depend on Python or JAX libraries.

The repository therefore does not claim to have injected and reproved the entire JAX API. A statement about every JAX function would require a fixed finite API surface and exact specifications for each operation. The current formalisation instead proves the concrete arithmetic, list, recurrence, GRU, optimizer, and state-transition functions actually used by the tracked learner.

No extra Python package is introduced merely to create a JAX-equivalence claim.

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
- pinned Nix composition.

## Documentation index

Generated from the tracked Markdown surface:

- `docs/agda-auto-proof-search.md` — Agda proof-search policy and concrete injectivity workflow.
- `docs/agda-smt-vehicle-boundary-2026-09-30.md` — SMT, Vehicle, GRU convergence, Baird, PPAD, and JAX boundaries.

The Markdown surface intentionally contains no external hyperlinks. The Elm presentation surface may contain navigational links to repository source.

## Maintenance rule

When a theorem appears to connect GRU dynamics with physics, economics, games, complexity, or external numerical behavior, its exact semantic bridge must appear as an Agda premise or proof. Graph discovery can suggest an edge; it cannot create the edge.
