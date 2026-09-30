# Agda proof search in this repository

## Proof authority

The repository has exactly two tracked Agda authority files:

- `FullCoupled/CanonicalLearnerMonolith.agda`
- `FullCoupled/TheoremsMonolith.agda`

Interactive proof search is a construction aid. An accepted Agda term is the authority. Mercury, Dhall, Mirth, Nix, Elm, SMT output, and graph search are supporting layers.

## Auto

Agda Auto searches for inhabitants of an interactive goal. A proposed term is still type-checked by Agda before it can be accepted.

Repository policy:

- keep committed theorem source free of unresolved holes;
- use Auto to discover small proof terms and decompositions;
- promote an accepted result to a named lemma or theorem;
- rerun the canonical batch check after promotion;
- let Mercury inspect the resulting declaration and its real dependencies.

## Search About

Search About is used when the primary problem is finding an existing declaration with the right type or name. It is particularly useful around equality, `List`, `Monoid`, injectivity, left-inverse, recurrence, and fixed-point vocabulary.

Use Search About when the candidate declaration is unknown. Use Auto when the candidate declarations are known and the remaining task is assembling the proof term.

## Concrete GRU left inverse and injectivity

The canonical statistical encoding includes the original `GRUState`. Its decoder is the first projection. The theorem monolith now makes the proof sequence explicit:

`canonicalGRUStatisticalDecodeEncode`

establishes the left inverse, then

`leftInverse-implies-injective`

derives injectivity, giving

`canonicalGRUStatisticalEncodeInjective`.

This proves injectivity of the observation encoding. It does not assert injectivity of the recurrent transition `gruStep`.

## Tail stability and the generic convergence kernel

The canonical learner already proves that the persistent GRU matrix/noise/control tail is unchanged over every iterate of the concrete learner. The reusable convergence theorem additionally requires an injective encoding, exact state/feature step conjugacy, and an eventually fixed feature tail.

Persistent-tail preservation is therefore a concrete lemma to reuse, not a substitute for the other premises.

## Canonical-learner Baird boundary

The generic arbitrary-weight/arbitrary-update Baird records have been removed.

The current declaration is `CanonicalLearnerBairdSevenStarBoundary K s`. It is indexed by the actual canonical learner and carries its already-proven persistent-GRU tail invariant. The numerical divergence result remains a supplied witness because the repository does not silently turn an empirical or literature claim into an Agda proof term.

## PPAD boundary

No PPAD-completeness theorem is promoted. A valid PPAD result would require a concrete search relation, totality, polynomial encoding bounds, membership, and an explicit hardness reduction. Fixed-point terminology alone is not sufficient.

## JAX boundary

No JAX module or dependency is tracked. There is consequently no whole-JAX API to prove by name. The repository proves the concrete functions that occur in the canonical learner instead of fabricating a universal JAX equivalence statement.

## Interactive launcher

The current interactive theorem path is:

`bash tools/agda-auto-session.sh FullCoupled/TheoremsMonolith.agda`

The repository-wide batch check remains authoritative after any interactive search session.

## JAX execution mirror

`tools/jax_reference.py` has a finite JAX execution mirror for every current JAX function. The theorem monolith gives each one a typed Agda counterpart collected by `JAXExecutionMirrorReproof`.

| JAX function | Agda counterpart |
| --- | --- |
| `vmap_affine` | `jaxVmapAffine` |
| `associative_prefix_sum` | `jaxAssociativePrefixSum` |
| `recurrent_scan` | `jaxRecurrentScan` |
| `lexicographic_score_order` | `jaxLexicographicScoreOrder` |
| `sparse_support_size` | `jaxSparseSupportSize` |
| `sparse_support_top_k` | `jaxSparseSupportTopK` |
| `sparsemax_policy_index` | `jaxSparsemaxPolicyIndex` |
| `integer_layernorm_centered_numerators` | `jaxIntegerLayerNormCenteredNumerators` |
| `integer_layernorm_radicand` | `jaxIntegerLayerNormRadicand` |
| `batched_integer_layernorm_radicand` | `jaxBatchedIntegerLayerNormRadicand` |
| `signed_gate` | `jaxSignedGate` |
| `gru_hidden_step` | `jaxGRUHiddenStep` |
| `batched_gru_hidden_step` | `jaxBatchedGRUHiddenStep` |
| `jitted_scan_sum` | `jaxJittedScanSum` |

The JAX algorithms are deliberately array-native where that is materially more efficient: `vmap` for independent maps, `lax.scan` for recurrence, `lax.associative_scan` for associative prefix work, `jnp.lexsort` for deterministic score ordering, one sorted prefix pass for sparse support, fixed-`k` `lax.top_k`, and exact `int64` arithmetic.

The Agda counterpart proves the finite computational law/equivalence. It does not claim that Agda has proved JAX's Python runtime, compiler, `jit`, or shape tracer.

## Presentation synchronization

The Elm Pages surface is independent of proof search. Mirth synchronizes the current monolith inventory and shared Agda import block.

## Pinned versions

- Agda 2.8.0
- agda-stdlib 2.3

Recheck this document when the proof-search commands, theorem paths, proof authority, or pinned versions change.
