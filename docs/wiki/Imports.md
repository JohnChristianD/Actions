# Imported Libraries and Verification Substrate

Last audited: 2026-09-19 against `main` after the automated e-graph correction.

## Canonical learner

### `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

Direct library surface:

- `Relation.Binary.PropositionalEquality`
- `Agda.Builtin.Nat`
- `Data.Nat`
- `Data.Fin`
- `Data.Fin.Properties`
- `Data.Nat.DivMod`
- `Data.Product`
- `Data.Empty`

The canonical learner is concrete. It does not depend on a broad abstract-algebra hierarchy.

## Canonical theorem monolith

### `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

Direct imports:

- `Relation.Binary.PropositionalEquality`
- `Agda.Builtin.Nat`
- `Data.Empty`
- `Data.Fin`
- `Data.Nat`
- `Data.List.Base`
- `CanonicalLearnerMonolith`

The theorem monolith proves laws over the existing learner definitions rather than rebuilding the learner implementation.

## Canonical finite environment surface

### `Exotic/ERL/FullCoupled/CanonicalGamePorts.agda`

Uses:

- propositional equality;
- natural numbers;
- finite indices;
- finite division/remainder utilities;
- products;
- `⊥`.

It defines exact finite state/transition ports.

### `Exotic/ERL/FullCoupled/CanonicalFaithfulGameVariants.agda`

Uses the game-port definitions plus finite arithmetic and products to define exact Toy Maze and FourRooms predicates.

### `Exotic/ERL/FullCoupled/CanonicalClosedLoopBench.agda`

Uses:

- propositional equality;
- natural numbers;
- finite indices and remainder;
- `CanonicalLearnerMonolith`;
- `CanonicalLearnerGameExecution_test`;
- `CanonicalGamePorts`.

It defines `ClosedLoopSpec`, `ClosedLoopRun`, `ClosedLoopMetrics`, and concrete finite benchmark specifications.

## Generalized benchmark surface

### `Exotic/ERL/FullCoupled/GeneralFullCoupledLearnerMonolith.agda`

The generalized learner adds standard-library order/sort structure, including:

- `Data.List.Sort`
- `Relation.Binary.Bundles.DecTotalOrder`
- `Relation.Binary.Construct.On`
- `Relation.Binary.Construct.Flip.EqAndOrd`
- `Data.Product.Relation.Binary.Lex.NonStrict`

It also uses finite/natural-number primitives and `Fin`.

This generalized surface is separate from the canonical learner.

## Mercury source surface

The current repository contains these Mercury modules in `.ci/discovery/`:

- `learner_semantic_extractor.m`
- `learner_semantic_manifest.m`
- `novel_learner_theorem_discovery.m`
- `symbolic_egraph.m`
- `symbolic_egraph_test.m`
- `interpolated_theorem_egraph.m`
- `interpolated_theorem_egraph_test.m`
- `prune_redundant_components.m`
- `prune_redundant_learner_modules.m`

The current Guix semantic-discovery path actively invokes the source extractor, manifest-driven discovery, the generic e-graph regression, and the manifest-derived interpolated e-graph regression. The two prune modules remain repository tooling, but they are not called by the current `.guix/ci.scm` semantic-discovery path.

### Forbidden-theorem scanner

`.ci/check_forbidden_theorems.m` scans the configured Agda proof files for forbidden theorem/axiom markers such as `postulate`, `?hole?`, and related unsafe surfaces.

It runs in the Guix `mercury` lane.

## Guix reproducibility layer

### `.guix/channels.scm`

- Guix branch: `version-1.5.0`
- channel commit: `ac03c482b1910a1672427beaea07ddcd1d652806`

### `.guix/manifest.scm`

- Agda 2.7.0.1
- Agda standard library 2.3
- Mercury 22.01.4
- Guile 3.0
- Git

No Python package is part of this pinned verification manifest.

## GitHub workflow surface

`.github/workflows/guix-composition.yml` currently defines:

- Guix / Agda `--safe` connected theorem surface;
- Guix / Mercury connected theorem and verifier lane;
- Guix / Mercury novel learner theorem discovery;
- Guix repository surface audit.

All execute through the pinned Guix manifest and `.guix/ci.scm`.

## Synchronization note

The current `.guix/ci.scm` safe-file list no longer names the removed `CanonicalClosedLoopInterface.agda`; the canonical closed-loop benchmark surface is `CanonicalClosedLoopBench.agda`.
