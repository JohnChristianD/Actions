# Unconditional finite-candidate price kernel — 2026-09-26

## Status

Implemented on branch `codex/unconditional-finite-price-kernel` in the canonical theorem monolith.

## Exact result

`FiniteCandidateDecision` gives an explicit two-way decision for a supporting relation at one allocation:

- `acceptCandidate`: a proof of the supporting relation;
- `rejectCandidate`: a proof that the supporting relation is impossible.

`finiteCandidatePriceSearch` then recursively scans any finite candidate-price list and returns exactly one of:

- a concrete `Σ Price (λ p → supports p allocation)` witness; or
- a list containing every supplied candidate together with a proof that each candidate fails the supporting relation.

The theorem is unconditional with respect to the supplied finite candidate list and decision procedure. It does not assert that a supporting price exists outside that list, and therefore does not conflict with `noUnconditionalMegaGeneralizedWalrasianExistence`.

## Boundary

This closes a constructive finite/discrete **candidate classification** kernel without adding imports. It does not close classical supporting-price derivation, separation/KKT construction, or unconditional Walrasian existence.

The canonical economic witness records remain contracts: a `SupportingPriceWitness` still requires an actual price and supporting proof.

## Verification target

The implementation uses only imports already present in `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`. Repository CI is the authoritative syntax/typecheck gate.
