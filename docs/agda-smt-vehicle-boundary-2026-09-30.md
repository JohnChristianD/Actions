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

All generic Baird records have been pruned from the active proof surface.

The surviving boundary is `CanonicalLearnerBairdSevenStarBoundary K s`, indexed by the actual canonical learner kernel and state. It carries the exact seven-state/eight-feature data, behavior probabilities, solid target, zero reward, 99/100 discount, feature equations, and the already-proved persistent-GRU tail invariant for `iterateCanonical`.

The divergence property is an explicit witness for that concrete learner. It is not manufactured from generic tail stability, graph search, or the convergence kernel.

## Physics and economics

The theorem monolith still contains the Hodge-Maxwell/four-law semantic surfaces, GRU/physics transport, economic production, demand and supply, aggregate excess-demand structures, supporting-price and market-clearing witnesses, Walrasian interfaces, and fixed-point/stationary/economic closures.

The injectivity/convergence machinery does not automatically identify those domains. Exact transport and interpretation premises remain explicit.

## PPAD-completeness boundary

No PPAD-completeness theorem is claimed. A genuine result needs an explicit search relation, polynomial-size encoding, totality, membership, and a concrete PPAD-hardness reduction. Those proof objects are not present.

## JAX execution mirror

The executable JAX surface is deliberately finite: `tools/jax_reference.py` mirrors the concrete learner algorithms where array execution is a meaningful replacement for scalar/recursive execution.

The mirror uses:

- `jax.vmap` for independent maps;
- `jax.lax.scan` for recurrent state-carrying execution;
- `jax.lax.associative_scan` for associative prefix accumulation;
- `jax.numpy.lexsort` for the score ordering used by the sparsemax surface;
- a one-sort/one-prefix-pass sparse-support computation, with `jax.lax.top_k` reserved for fixed-`k` specialization;
- exact `int64` integer LayerNorm arithmetic;
- the concrete GRU hidden-state equation from the canonical learner.

The sparse-support mirror is the principal algorithmic improvement: it avoids repeatedly reconstructing `topCodes k xs` while testing every candidate `k`. The JAX implementation computes the descending magnitudes once, computes all prefix sums once, and evaluates the support inequalities in one vectorized pass.

The workflow pins JAX 0.11.2 and validates the mirror with `jax.jit` and `jax.eval_shape`. No extra ML framework or Python algorithm package is added. The Agda theorem surface remains the semantic authority, and proof terms are not replaced by JAX execution.

## Presentation and CI

Pages uses pure Elm. Mirth handles fast-dirty synchronization. Mercury performs declaration and graph analysis. Dhall expresses CI contracts. Nix supplies pinned toolchain composition.

None of those layers can promote an unproved semantic edge into an Agda theorem.


## Python boundary

Python is isolated to the dedicated JAX workflow because JAX itself is a Python package. The Nix shell and non-JAX CI helpers do not contain Python invocations.

## Markdown contract

Tracked Markdown is link-free; navigation belongs in the Elm presentation.
