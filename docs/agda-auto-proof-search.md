# Agda proof surface

## Authority

Exactly two Agda sources are active: `FullCoupled/CanonicalLearnerMonolith.agda` and `FullCoupled/TheoremsMonolith.agda`.

An accepted Agda term is authoritative. Mercury, Dhall, Mirth, Nix, SMT, Vehicle, JAX algorithm contracts, and Elm are supporting layers.

## GRU left inverse and injectivity

The canonical statistical observation contains the original `GRUState`; its decoder is first projection.

The accepted chain is `canonicalGRUStatisticalDecodeEncode` → `canonicalGRUStatisticalEncodeLeftInverse` → `leftInverse-implies-injective` → `canonicalGRUStatisticalEncodeInjective`.

`CanonicalGRUStatisticalInjectivityTheorem` packages the result. It proves injectivity of the observation encoding, not injectivity of `gruStep`.

`GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem` composes that injectivity with exact step conjugacy and an eventually fixed feature tail. It yields tail-fixed source state, eventual stationarity, and identifiability.

## Canonical Baird boundary

The active Baird construction is specialized to the already-tail-stable canonical learner. There is no generic Baird record.

`CanonicalLearnerBairdSevenStarWitness K s` carries the seven-state/eight-feature construction, 6/7 and 1/7 behavior, solid target, zero reward, 99/100 discount, upper/lower feature equations, the canonical persistent-GRU iterate tail, and an explicit divergence witness.

The tail field is exactly `canonicalPersistentGRU-afterFullStep-iterate K n s`. Baird is therefore downstream of the canonical learner proof rather than a generic state-transition schema.

## Retained sparsity theorems

L1 and 1-path-norm definitions, wrappers, and theorems are no longer active. They were not required by the canonical theorem obligations.

The retained hard-sparsity result is `CanonicalHardSparsityDegeneracyTheorem`, the exact zero-threshold equivalence between `HardSparse K s` and `SoftSparseBounded K s zero`.

The retained finite Tsallis-2 surface is `ActionWeights`, `actionSupportCount`, `actionWeightSum`, `actionWeightSquareSum`, `generalTsallis2Denominator`, `generalTsallis2Numerator`, `generalTsallis2NearSparsity`, its zero/nonzero-definition laws, `generalSupportSparsity`, and `UniformSupportTsallisBoundary`.

These are finite constructive definitions and equalities. Continuous Shannon or analytic regularity is not inferred.

## Physics, economics, and PPAD

Physics and economics remain active theorem families: Hodge-Maxwell/four-law interfaces, GRU/physics transport, production, demand/supply, excess demand, market-clearing and supporting-price witnesses, Walrasian interfaces, stationary/fixed-point closures, and economic composition.

No PPAD-completeness theorem is claimed. A genuine completeness proof requires an explicit polynomial-size total search relation, encoding-size bounds, membership, and a hardness reduction.

## JAX algorithm contracts

The repository no longer contains the Python JAX wrapper. The retained JAX-facing surface is `JAXExecutionMirrorReproof`.

Its finite Agda contracts cover vectorized affine mapping, associative prefix execution, recurrent scan, lexicographic ordering, sparse-support size/top-k/policy selection, integer LayerNorm, signed gating, scalar/batched GRU hidden updates, Tsallis-2 near-sparsity, support sparsity, and scan-sum.

The prefix and batched-GRU record fields are exact laws against their finite Agda implementations rather than tautological self-equalities. The contracts prove the finite algorithm semantics; they do not prove Python/JAX compiler behavior.

## Mirth synchronization and concurrency

The learner common-import block is the synchronization source of truth. The Mirth synchronizer checks marker cardinality, exact byte equality, dependency direction, canonical learner import count, and external SMT/Z3/Vehicle counts.

Independent predicates run concurrently, every child status is collected, and the aggregate fails if any predicate fails. Write mode uses a bounded directory lock and replaces the theorem block only after a complete candidate has been constructed.

The Mirth graph program also runs independent learner/theorem extraction passes concurrently and emits deterministic nodes and edges. The graph is source-derived, not an Agda elaboration.

## Exhaustive Elm relation view

The generated Elm graph contains every declaration/reference edge produced by the source parser for the two active monoliths. The Pages UI exposes the complete generated edge list, declaration search, learner/theorem filtering, selected-node detail, incoming/outgoing relations, relation counts, and a dynamic SVG neighborhood.

This is Mermaid-like interaction implemented in pure Elm. No Mermaid runtime is required.

## Toolchain

Agda is pinned to 2.8.0 with standard library 2.3. No Python source file or shell-script file is required by the active repository surface.

Tracked Markdown is link-free.
