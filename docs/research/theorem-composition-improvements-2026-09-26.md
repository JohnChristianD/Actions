# Theorem composition improvements — 2026-09-26

## Scope

This pass closes the strongest proof-relevant composition seams identified in the canonical learner theorem graph. The source of proof authority remains `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`; Mermaid remains a projection.

## Closed improvements

### 1. Arbitrary-length token generation

Added `CanonicalTokenArbitraryLengthGenerationTheorem` and
`canonical-token-arbitrary-length-generation-theorem`.

The package consumes the existing:

- `canonicalTokenStep-conjugacy`
- `canonicalTokenListState-conjugacy`
- `canonicalToken-prefix-monoid-homomorphism`
- `canonicalTokenLogitTrace-append`

It exposes exact state conjugacy, prefix-monoid structure, and arbitrary finite-list logit-trace append composition in one proof-relevant record. This closes the previously documented gap where the constituent theorems existed but no single record packaged the full arbitrary-length generation surface.

The construction matches the standard algebraic picture: finite lists form the free monoid on a token set, and a set action extends to a free-monoid action whose concatenation law composes successive state transformations. urlnLab: actionhttps://ncatlab.org/nlab/show/action urlnLab: free monoidhttps://ncatlab.org/nlab/show/free%2Bmonoid

### 2. Orbit injectivity

The canonical learner already had `canonicalOrbit-state-injective` after the clock-removal work, so no duplicate theorem was added.

The generic frontier was strengthened instead with `NatSuccessorProgressWitness`, `successorMeasureAfterIterate`, and `successorMeasureOrbitInjective`. This factors the reusable mathematical kernel away from the canonical learner: an exact successor-valued measure gives injective orbit indices by cancellation.

The canonical `totalCount` witness remains the concrete instance. This is strictly stronger as an API boundary than repeating the learner-specific proof while preserving the existing theorem name and graph surface.

### 3. Iterated F4 / NormPair factor stability

Added `CanonicalF4NormPairIterateFactorStabilityTheorem` and
`canonical-f4-normPair-iterate-factor-stability-theorem`.

The package combines the already-closed F4/NormPair one-step factor theorem with:

- iterated `normPairWeightPlusOne` invariance,
- iterated persistent-GRU invariance,
- iterated NormPair quotient compatibility.

This makes the downstream iterate-stability interface explicit without claiming convergence, equilibrium, or an economic existence theorem.

## Boundary retained

No new Hodge-Maxwell inhabitant, equilibrium witness, market-clearing witness, supporting-price witness, or stationary-measure conclusion is manufactured by this pass. Those remain explicit conditional/frontier interfaces.

## Graph policy

The graph now exposes the three closed seams, while proof authority remains the Agda theorem monolith. A graph edge is not treated as proof evidence.

## Verification status

The branch was created from current `main` and all source mutations were made through the repository's GitHub API surface. Agda/Mercury execution still needs the repository CI gate; no local Agda toolchain was available in this execution environment.

## Provenance

Before: existing component theorems and graph candidates.

Change: package the arbitrary-length token generation closure, factor the reusable successor-measure orbit injection kernel, and package iterated F4/NormPair factor stability.

Why: remove duplicated proof topology, close real composition seams, and keep conditional cross-domain claims witness-gated.

