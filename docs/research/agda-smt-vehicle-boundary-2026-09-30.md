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

Schmitty is installed as an Agda library on the same single latest Agda toolchain used by the canonical workflow. The Schmitty CI lane verifies the installed library registration and trusted Z3 executable without creating a temporary `.agda` probe. The canonical proof lanes remain:

```sh
$AGDA_COMMAND --safe -l standard-library -i . Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
$AGDA_COMMAND --safe -l standard-library -i . Exotic/ERL/FullCoupled/TheoremsMonolith.agda
```

The Pages surface is independent of SMT and Vehicle: it is a static Elm presentation over the two canonical monolith names. No Mirth compiler, Mirth source, generated Agda source, or unsupported Mirth runtime participates in CI.

Stale when: Schmitty release, Z3 setup action, canonical Agda/std-lib versions, Vehicle Agda-library dependency, or theorem-graph authority changes.
