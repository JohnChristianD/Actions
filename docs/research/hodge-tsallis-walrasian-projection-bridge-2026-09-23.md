# Hodge-Maxwell/Tsallis/Walrasian projection bridge — 2026-09-23

## Decision

The Maxwell/Hodge-Maxwell composition has been generalized from a finite carrier to an arbitrary carrier. The canonical continuous representation surface is:

- `ContinuousHodgeMaxwellExactRepresentationData`
- `ConnectedContinuousHodgeMaxwellGRURepresentationTheorem`
- `ConnectedMaxwellTsallisExactConjugacyTheorem`
- `HodgeMaxwellMiddleDegreeInvolutionTransportTheorem`
- `ConnectedHodgeMaxwellTsallisDivergenceCompositionTheorem`
- `ConnectedHodgeMaxwellTsallisIdempotentProjectionTheorem`
- `ConnectedHodgeMaxwellTsallisWalrasianProjectionClosureTheorem`

The continuous representation certificate carries exact differential-form Maxwell equations, explicit continuity predicates, exact encode/decode laws yielding a global `StateIsomorphism`, and exact recurrent-step conjugacy. The explicit global encode-injectivity theorem is a direct consequence of the encode/decode inverse laws.

## What changed

The prior Maxwell/Hodge-Maxwell theorem family was tied to `Fin n` carriers and finite discretization certificates. Those theorems have been removed from the canonical Maxwell/Hodge-Maxwell composition because their carrier dependency was intrinsic rather than incidental.

The generic Maxwell/Tsallis carrier is now a `Set`. The divergence structure is likewise carrier-polymorphic. The idempotent transport record no longer has a finite-carrier name or dependency.

The old finite-carrier pigeonhole impossibility theorem is intentionally pruned. Its contradiction specifically requires a map into `Fin n`; replacing that finite carrier by `ℤ` would invalidate the pigeonhole conclusion rather than preserve it.

## Continuous Maxwell scope

The new theorem is an exact conditional representation schema, not a universal existence theorem. A caller must still supply:

- the differential-form/function-space semantics;
- the manifold/domain/metric/source/boundary structure needed by the intended physical model;
- continuity witnesses for the declared operators and maps;
- an exact encoder/decoder to the chosen GRU carrier;
- exact recurrent-step conjugacy.

Therefore the graph now supports a genuine continuous, non-finite Maxwell/Hodge-Maxwell composition without claiming that every infinite-dimensional Maxwell solution space is isomorphic to a particular GRU state space.

## Hodge-star involution

`HodgeMaxwellMiddleDegreeInvolutionTransportTheorem` now consumes the carrier-polymorphic continuous representation directly. Its proof remains conditional on an explicit GRU-side involution and observed factorization:

`observe(star(star(s))) = observe(s)`

plus left-invertibility yields

`star(star(s)) = s`.

This does not make the raw Hodge-star square law unconditional. The degree, signature, metric, and the exact declared Hodge action still matter.

## Z versus Nat

`ℤ` is retained as the exact unbounded algebraic carrier where the canonical learner uses integer semantics. It is not a universal carrier for arbitrary continuous Maxwell function spaces.

`Nat` remains appropriate for iteration/horizon indexing and countability witnesses. It is no longer used as the cardinality parameter of the Maxwell/Hodge-Maxwell representation family.

## Verification boundary

The repository does not infer analytic existence, smoothness, convexity, Fenchel/Legendre duality, or universal continuous Maxwell representation from the integer-ring upgrade alone.

The canonical proof authority remains Agda `--safe`; graph search and e-graph synchronization are discovery/verification infrastructure rather than proofs by themselves.
