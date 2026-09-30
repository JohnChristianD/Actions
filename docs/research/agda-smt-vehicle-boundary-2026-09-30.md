# Agda SMT automation and Vehicle boundary — 2026-09-30

## Scope

This note defines the interoperability boundary for external SMT assistance and Vehicle-derived formalisation. The tracked Agda source surface is strictly two monoliths: `CanonicalLearnerMonolith.agda` and `TheoremsMonolith.agda`.

## Schmitty

Schmitty v1.0.1 supplies Agda SMT reflection and a Z3 backend. Its integration examples use `{-# OPTIONS --allow-exec #-}` and `solveZ3`. The repository does not retain a third tracked Schmitty Agda module: CI generates `SchmittyCIProbe.agda` in a temporary directory, runs it with the Schmitty-compatible Agda 2.6.2.2 / standard-library 1.7.1 toolchain, then deletes it.

The canonical proof environment remains Agda 2.8.0.2 with standard-library 2.4. `--safe` remains enabled for both canonical monoliths. `--allow-exec` is limited to the temporary Schmitty probe; it is never added to canonical proof authority.

The CI Schmitty lane does not import or rewrite the theorem monolith. It proves independent integer normalization witnesses with `solveZ3`. `TheoremsMonolith.agda` retains only the safe mirror already discharged by `IntegerRingSolver`.

## Vehicle

Vehicle is an upstream Haskell tool with an Agda backend. Its current `vehicle-agda/vehicle.agda-lib` declares `depend: standard-library-2.3`, while this repository's canonical proof environment uses standard-library 2.4. The upstream repository is Cabal-based rather than a Haskell Vehicle package exposed by this repository's pinned nixpkgs.

No current Vehicle output establishes a repository-specific emergent composition theorem. Vehicle's normalisation code is compositional internally, but that is implementation structure, not a theorem about this repository's learner/economic semantics. Therefore no Vehicle theorem is promoted into `TheoremsMonolith.agda` or the Mercury theorem graph in this batch.

A future Vehicle bridge requires:
- a pinned upstream Vehicle revision;
- a checked Vehicle/Agda stdlib compatibility layer;
- an explicit translation theorem into this repository's carrier/semantic interfaces;
- graph insertion only after the translated proposition is present and proved on one of the two canonical monoliths.

## Graph boundary

Mercury graph topology continues to derive from `TheoremsMonolith.agda`. Schmitty is evidence-only automation. Vehicle remains an external compatibility candidate. Neither creates graph edges or theorem nodes by conceptual similarity.

The graph gate remains:
- real Agda dependency edges only;
- A* cost guides traversal, never equality;
- emergent-composition reporting cannot promote unproved external statements;
- review frontier remains source-derived.

## Verification boundary

Schmitty lane:
```sh
# CI-generated temporary source only
agda -v0 -l standard-library -l schmitty -i "$PROBE_DIR" "$PROBE_DIR/SchmittyCIProbe.agda"
```

Canonical proof lanes:
```sh
$AGDA_COMMAND --safe -l standard-library -i . Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
$AGDA_COMMAND --safe -l standard-library -i . Exotic/ERL/FullCoupled/TheoremsMonolith.agda
```

Mirth remains source-to-presentation synchronization only. Dhall remains CI contract/orchestration. Nix remains reproducible tool provisioning. Markdown remains generated-index/documentation surface.

Stale when: Schmitty release, Z3 setup action, canonical Agda/std-lib versions, Vehicle Agda-library dependency, or theorem-graph authority changes.
