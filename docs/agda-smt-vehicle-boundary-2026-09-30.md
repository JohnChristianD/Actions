# Agda SMT automation and Vehicle boundary — 2026-09-30

## Scope

The tracked Agda surface is exactly:

- `FullCoupled/CanonicalLearnerMonolith.agda`
- `FullCoupled/TheoremsMonolith.agda`

The learner is checked independently. The theorem monolith is the sole derived-semantic consumer of the canonical learner.

## Schmitty

The theorem monolith exposes a closed integer normalization fact through Schmitty and the Z3 backend. The external solver is an automation boundary, not an independent proof authority: Agda checks the resulting theorem term.

The current CI contract checks the pinned Schmitty Agda source, its library metadata, its Agda-compatible version, and the Z3 executable before the theorem check.

## Vehicle

Vehicle is consumed at its pinned Agda reflection/interface boundary. The repository does not treat a standalone Vehicle compiler build as proof authority and does not add a third tracked Agda source module.

## Import synchronization

The two monoliths share one exact common import block. Mirth treats the learner block as the source of truth.

The theorem monolith may then add theorem-specific imports for Schmitty, Vehicle, induction, arithmetic, algebraic tactics, effect/state, and list-effect support. The only cross-monolith import is:

`open import FullCoupled.CanonicalLearnerMonolith as C`

The learner does not import the theorem monolith.

## GRU left inverse and injectivity

The canonical statistical encoding explicitly contains the original `GRUState`, and its decoder returns that state by first projection.

The theorem surface proves the left inverse and then derives injectivity:

`canonicalGRUStatisticalDecodeEncode`

followed by

`leftInverse-implies-injective`

and

`canonicalGRUStatisticalEncodeInjective`.

This is an encoding theorem. It does not imply that `gruStep` is injective.

## Canonical tail stability

The learner monolith proves persistence of the GRU matrix/noise/control tail under each GRU step. The theorem monolith also proves the persistence over every full-learner iterate.

That concrete result is the learner-side tail fact used by the canonical Baird boundary and as a candidate ingredient for the generic convergence kernel.

## Canonical-learner Baird boundary

Generic Baird records have been pruned.

The current Baird package is `CanonicalLearnerBairdSevenStarBoundary K s`. It fixes the seven-state/eight-feature construction and carries the actual canonical learner kernel/state plus the already-proved persistent-GRU tail theorem.

Its divergence field is an explicit witness. Tail stability, injectivity, or graph search is not allowed to synthesize that divergence claim.

## Physics and economics

The theorem monolith still contains the Hodge-Maxwell/four-law semantic surfaces, GRU/physics transport, economic production, demand and supply, aggregate excess-demand structures, supporting-price and market-clearing witnesses, Walrasian interfaces, and fixed-point/stationary/economic closures.

The injectivity/convergence machinery does not automatically identify those domains. Exact transport and interpretation premises remain explicit.

## PPAD-completeness boundary

No PPAD-completeness theorem is claimed. A genuine result needs an explicit search relation, polynomial-size encoding, totality, membership, and a concrete PPAD-hardness reduction. Those proof objects are not present.

## JAX boundary

No JAX source or dependency is tracked. The repository therefore makes no whole-JAX equivalence claim and adds no Python/JAX package merely to create one.

## Presentation and CI

Pages uses pure Elm. Mirth handles fast-dirty synchronization. Mercury performs declaration and graph analysis. Dhall expresses CI contracts. Nix supplies pinned toolchain composition.

None of those layers can promote an unproved semantic edge into an Agda theorem.
