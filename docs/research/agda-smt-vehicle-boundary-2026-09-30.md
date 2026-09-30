# Agda SMT automation and Vehicle boundary — 2026-09-30

## Scope

This note defines the interoperability boundary for external SMT assistance and Vehicle-derived formalisation. The tracked Agda source surface is strictly two monoliths: `CanonicalLearnerMonolith.agda` and `TheoremsMonolith.agda`.

## Schmitty

Schmitty v1.0.1 supplies Agda SMT reflection and a Z3 backend. Its upstream examples use `{-# OPTIONS --allow-exec #-}` and `solveZ3`. This repository does not add those execution options to either canonical proof monolith; the Schmitty lane is non-authoritative installation/trust verification only.
Mercury graph topology continues to derive from `TheoremsMonolith.agda`. Schmitty is evidence-only automation. Vehicle remains an external compatibility candidate. Neither creates graph edges or theorem nodes by conceptual similarity.

The graph gate remains:
- real Agda dependency edges only;
- A* cost guides traversal, never equality;
- emergent-composition reporting cannot promote unproved external statements;
- review frontier remains source-derived.

## Verification boundary

Schmitty is installed on the same single latest Agda toolchain used by the canonical workflow, and the theorem monolith consumes its Int/Z3 import surface directly. Vehicle's current Agda reflection interface is likewise imported by the theorem monolith from the pinned Vehicle source tree; no third tracked Agda source is introduced. The theorem lane uses the current integration flags rather than a second Agda version:

```sh
$AGDA_COMMAND --allow-exec -l standard-library -i . -i "$VEHICLE_AGDA_SOURCE" -i "$SCHMITTY_AGDA_SOURCE" -i "$AGDARSEC_AGDA_SOURCE" Exotic/ERL/FullCoupled/TheoremsMonolith.agda
```

The Pages surface is independent of the unsupported Mirth compiler path. Mirth remains a source-level fast-dirty synchronization/orchestration layer; its Mirth-to-C99 compilation is explicitly outside the repository's supported verification workflow.

Stale when: Schmitty release, Z3 setup action, canonical Agda/std-lib versions, Vehicle Agda-library dependency, or theorem-graph authority changes.


## Tail-stability and convergence boundary

The repository distinguishes arbitrary long-run convergence from the stronger case already established by an exact eventual-stability witness. The integer LayerNorm A* layer has an explicit infinite stable tail and a semantic convergence transport; once the representation is constant from some index onward, the corresponding discrete representation sequence is eventually equal to its target. This is the convergence seam used by the theorem graph, not a blanket convergence theorem for every learner quantity or every economic process.
