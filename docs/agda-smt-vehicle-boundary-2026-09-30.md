# Agda SMT automation and Vehicle boundary — 2026-09-30

## Scope

The active Agda surface is exactly:

- `FullCoupled/CanonicalLearnerMonolith.agda`
- `FullCoupled/TheoremsMonolith.agda`

The learner is checked independently. The theorem monolith is the sole derived-semantic consumer.

## Schmitty and Z3

The theorem monolith exposes a closed integer normalization fact through Schmitty and the Z3 backend. The external solver is an automation boundary. Agda checks the resulting theorem term.

The CI contract verifies the pinned Schmitty Agda source, its library metadata, the compatible Agda version, and the Z3 executable before the theorem check.

## Vehicle

Vehicle is consumed at its pinned Agda reflection/interface boundary. It is not treated as a standalone theorem authority, and no third tracked Agda source is introduced for it.

## Mirth import synchronization

The two monoliths share one byte-identical common import block. The learner block is the source of truth.

The theorem monolith may add theorem-specific imports for Schmitty, Vehicle, induction, arithmetic, algebraic tactics, effect/state, and list-effect support. The only cross-monolith import is:

`open import FullCoupled.CanonicalLearnerMonolith as C`

The learner never imports the theorem monolith.

The synchronizer verifies marker counts, byte identity, directionality, and external import counts. Independent predicates execute concurrently and their exit statuses are aggregated. Write mode uses an atomic directory lock with bounded retry and an atomic candidate replacement.

## Agda declaration graph

The Mirth graph generator reads both active monoliths. It records every top-level declaration in its source model and scans each declaration body for references to the complete declaration set.

The generated graph contains source-tagged nodes and directed reference edges. Edges are deduplicated and sorted. The Pages application receives the complete generated dataset and exposes all recorded incoming and outgoing relations for the selected declaration.

This is a source-derived declaration graph, not a substitute for Agda elaboration or type checking.

## GRU left inverse and injectivity

The canonical statistical observation contains the original `GRUState`. Its decoder returns that state by first projection.

The accepted chain is:

`canonicalGRUStatisticalDecodeEncode`

→ `canonicalGRUStatisticalEncodeLeftInverse`

→ `leftInverse-implies-injective`

→ `canonicalGRUStatisticalEncodeInjective`.

This is an encoding theorem. It does not imply that `gruStep` is injective.

## Canonical tail stability and convergence

The learner proves persistent-GRU tail preservation under the full learner step and lifts that equality to arbitrary learner iterates.

`GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem` composes injective observation, exact step conjugacy, and eventual feature-tail fixation. It derives source tail fixation, eventual stationarity, and identifiability.

## Canonical-learner Baird boundary

There is no generic Baird record.

`CanonicalLearnerBairdSevenStarWitness K s` is attached to the canonical learner kernel/state at the boundary. Its learner-tail field is the already-proved `canonicalPersistentGRU-afterFullStep-iterate K n s` theorem.

The construction records seven states, eight features, 6/7 versus 1/7 behavior, a solid target, zero reward, 99/100 discount, the upper/lower feature equations, and the explicit divergence witness.

## Hidden-Synergy, hard sparsity, and Tsallis-2

The finite L1/1-path surface remains active through:

`rowL1`, `weightL1`, `onePathVector`, `onePathNorm`, `rowL1OnesAbs`, `onePathOneLayer`, `HiddenSynergyNormPair`, `layerNormPair`, and `hiddenSynergy-one-layer-exact`.

The zero-threshold hard/soft sparse equivalence remains packaged as `CanonicalHardSparsityDegeneracyTheorem`.

The finite Tsallis-2 definitions and theorems remain present through `generalTsallis2NearSparsity`, its zero and nonzero-definition lemmas, `generalSupportSparsity`, and `UniformSupportTsallisBoundary`.

## Physics and economics

Physics and economics were not removed.

The theorem surface still carries Hodge-Maxwell/four-law semantic structures, GRU/physics transport, production, demand/supply, aggregate excess-demand, supporting-price and market-clearing witnesses, Walrasian interfaces, stationary/fixed-point closures, and economic composition.

Redundant wrappers were pruned where existing closures already carried the same semantic content. Domain definitions and their surviving proofs remain.

## PPAD boundary

No PPAD-completeness theorem is claimed. Fixed-point and equilibrium definitions are not treated as a substitute for PPAD membership and hardness proofs.

The missing proof obligations are explicit: a total polynomial-size search relation, encoding-size bounds, membership in PPAD, and a concrete hardness reduction.

## JAX execution and Agda reproof

`tools/jax_reference.py` is the only Python execution boundary. Its third-party imports are limited to JAX itself.

Every current JAX function has a named Agda mirror collected under `JAXExecutionMirrorReproof`.

The execution mirror uses JAX-native vectorization and scan primitives where appropriate and exact int64 arithmetic for the integer kernels. The Agda side checks finite computational laws and equivalence to canonical definitions; it does not claim to model the JAX compiler.

The non-JAX Nix shell, Mirth programs, Dhall orchestration, and shell helpers do not install Python packages.

## Mercury

Mercury's theorem graph and e-graph are semantic discovery and closure machinery. The active theorem registry is reconciled against the current Agda monolith so stale historical targets are not promoted.

The semantic frontier is separate from the exhaustive Mirth declaration-reference graph.

## Pure Elm presentation

The Pages application is pure Elm. It consumes generated graph data and does not execute proof, solver, or JAX code at runtime.

The page exposes declaration search, source filtering, complete selected-node incoming/outgoing relations, relation counts, and a dynamic SVG neighborhood.

No Mermaid runtime is required.

## Markdown contract

Tracked Markdown is link-free. Source navigation and interactive graph exploration belong in the Elm presentation.

No Markdown URL or Markdown link is used in this document.
