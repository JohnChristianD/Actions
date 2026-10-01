# Agda proof search in this repository

## Authority

Exactly two Agda source files are active:

- `FullCoupled/CanonicalLearnerMonolith.agda`
- `FullCoupled/TheoremsMonolith.agda`

Interactive proof search is a construction aid. An accepted Agda term is authoritative. Mercury, Dhall, Mirth, Nix, SMT, Vehicle, JAX, and Elm are supporting layers.

## GRU left inverse and injectivity

The canonical statistical observation contains the original `GRUState`, and the decoder returns it by first projection.

The proof chain is:

`canonicalGRUStatisticalDecodeEncode` → `canonicalGRUStatisticalEncodeLeftInverse` → `leftInverse-implies-injective` → `canonicalGRUStatisticalEncodeInjective`.

The packaged theorem is `CanonicalGRUStatisticalInjectivityTheorem`.

This establishes injectivity of the observation encoding. It is deliberately not described as injectivity of `gruStep`.

## Tail stability and the convergence kernel

The learner proves preservation of its persistent matrix/noise/control GRU tail under one full learner step and transports that equality through arbitrary full-learner iterates.

`GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem` is the reusable composition kernel. Its premises are explicit:

- an injective encoding;
- exact state/feature step conjugacy;
- an eventually fixed feature tail.

Its conclusions are tail-fixed source state, eventual stationarity, and identifiability. It does not create physics, economics, or Baird witnesses.

## Canonical-learner Baird construction

There is no generic Baird record in the active surface.

`CanonicalLearnerBairdSevenStarWitness K s` is the concrete boundary package. It is tied to the canonical learner kernel/state supplied at that boundary. Its tail field is exactly `canonicalPersistentGRU-afterFullStep-iterate K n s`, already proved by the learner/theorem surface.

The witness fixes the seven-state/eight-feature configuration, 6/7 versus 1/7 behavior, solid target, zero reward, 99/100 discount, upper/lower feature equations, and an explicit divergence witness.

The important distinction is structural: the Baird construction is attached to the already-tail-stable canonical learner, not to an arbitrary state-transition schema.

## Hidden-Synergy finite theorem surface

The retained finite L1/1-path definitions are:

`rowL1`, `weightL1`, `onePathVector`, `onePathNorm`, `rowL1OnesAbs`, `onePathOneLayer`, `HiddenSynergyNormPair`, `layerNormPair`, and `hiddenSynergy-one-layer-exact`.

The zero-threshold hard/soft sparse equivalence is packaged as `CanonicalHardSparsityDegeneracyTheorem`.

The finite Tsallis-2 surface remains explicit:

`ActionWeights`, `actionSupportCount`, `actionWeightSum`, `actionWeightSquareSum`, `generalTsallis2Denominator`, `generalTsallis2Numerator`, `generalTsallis2NearSparsity`, `generalTsallis2NearSparsity-zero`, `generalTsallis2NearSparsity-definition`, `generalSupportSparsity`, and `UniformSupportTsallisBoundary`.

These are exact finite definitions and equalities. Continuous Shannon or analytic regularity claims are not inferred from them.

## Physics and economics

Physics and economics remain active theorem families.

The surface still contains Hodge-Maxwell/four-law interfaces, GRU/physics transport, production, demand/supply, aggregate excess-demand structures, market-clearing and supporting-price witnesses, Walrasian interfaces, stationary/fixed-point closures, and economic composition.

Only redundant wrapper endpoints were pruned. The domain structures themselves remain.

## PPAD-completeness boundary

No PPAD-completeness theorem is present.

A completeness proof would need a total polynomial-size search relation, explicit encoding-size bounds, a PPAD membership argument, and a concrete hardness reduction. Existing fixed-point/equilibrium definitions do not substitute for those proof obligations.

## JAX reproof

The JAX boundary contains exactly the current executable kernels:

`vmap_affine`, `associative_prefix_sum`, `recurrent_scan`, `lexicographic_score_order`, `sparse_support_size`, `sparse_support_top_k`, `sparsemax_policy_index`, `l1_row`, `l1_matrix`, `one_path_norm`, `tsallis2_near_sparsity_fraction`, `support_sparsity_fraction`, `integer_layernorm_centered_numerators`, `integer_layernorm_radicand`, `batched_integer_layernorm_radicand`, `signed_gate`, `gru_hidden_step`, `batched_gru_hidden_step`, and `jitted_scan_sum`.

Every current JAX kernel has a named Agda mirror in `JAXExecutionMirrorReproof`.

The execution choices are intentionally JAX-native: vectorization with `vmap`, associative prefix execution with `lax.associative_scan`, stateful scans with `lax.scan`, deterministic lexicographic ordering with `jnp.lexsort`, one ordered sparse-support prefix, fixed-k `lax.top_k`, fused reductions, and exact int64 arithmetic.

The Agda side proves finite typed laws relating these mirrors to the canonical definitions. It does not pretend to prove JAX compiler internals.

## Mirth import synchronization

The learner common-import block is the source of truth.

The synchronizer checks marker cardinality, exact block equality, dependency direction, canonical learner import count, and external SMT/Z3/Vehicle import counts. Independent predicates run concurrently; failures are aggregated instead of being lost through the first failed child. Write mode is protected by an atomic directory lock and replaces the theorem block only after the complete candidate is produced.

## Agda declaration graph

The Mirth graph generator reads both monoliths before Elm compilation.

Its source model records top-level declarations from both files and creates directed declaration-reference edges by scanning each declaration body against the complete declaration set. Nodes and edges are deduplicated and sorted before being emitted as Elm data.

The Pages UI exposes the complete generated edge set through search, filtering, selected-node detail, and incoming/outgoing relation lists. The SVG view is a pure-Elm visualization of that generated relation data.

The graph is a source parser, not an Agda elaborator. Proof authority remains the accepted Agda term.

## Toolchain boundary

The non-JAX repository tooling contains no Python package dependency. Python is isolated to the JAX workflow, whose third-party dependency is JAX itself.

The Agda toolchain is pinned to Agda 2.8.0 with standard library 2.3.

No Markdown links are used in this document.
