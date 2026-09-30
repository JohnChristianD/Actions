# Agda SMT automation and Vehicle boundary — 2026-09-30

## Scope

This note defines the interoperability boundary for external SMT assistance and Vehicle-derived formalisation. It does not change the proof authority: the two canonical theorem monoliths remain the only semantic source files checked with Agda `--safe`.

## Schmitty

Schmitty v1.0.1 supplies Agda SMT reflection and a Z3 backend. Its own integration examples use `{-# OPTIONS --allow-exec #-}` and `solveZ3`. That execution capability is deliberately isolated under `ProofAutomation/SchmittyAssisted.agda`.

The CI lane therefore uses the Schmitty-compatible Agda 2.6.2.2 / standard-library 1.7.1 environment rather than changing the repository's canonical Agda 2.8.0.2 / standard-library 2.4 proof environment. The lane checks the Z3 executable and the external SMT proof, then separately runs the normal safe proof lanes.

The safe theorem surface does not import Schmitty. `TheoremsMonolith.agda` carries a `SchmittySafeSMTBoundaryTheorem` record whose witness is the existing safe `IntegerRingSolver` proof. The SMT run is evidence of an independent automation path, not a proof-authority substitution.

## Vehicle

Vehicle is treated as a future interoperability source. Its current `vehicle-agda` library declares a dependency on standard-library 2.3, while this repository's proof CI uses standard-library 2.4. Because the version boundary is explicit, the current change does not add Vehicle modules to the canonical theorem imports or synthesize Vehicle claims into the theorem graph.

A future Vehicle bridge should be a separate compatibility package with:
- a pinned Vehicle revision;
- an explicit stdlib compatibility test;
- a translation theorem into the repository's existing carrier/semantic interfaces;
- no second learner/economic theorem authority.

## Graph boundary

The Mercury graph continues to derive topology from `TheoremsMonolith.agda`. The new Schmitty surface is intentionally record-packaged so it documents the automation boundary without presenting external SMT execution as a new nonredundant domain theorem. The existing A* graph search, emergent-composition reporting, and dominance/pruning checks remain authoritative for topology.

## Verification

The new CI lane is named `Schmitty`. It runs:
```sh
Z3 -version
AGDA_SCHMITTY_COMMAND --allow-exec -i . ProofAutomation/SchmittyAssisted.agda
```
The regular `AgdaSafe` lane still checks:
```sh
AGDA_COMMAND --safe -l standard-library -i . Exotic/ERL/FullCoupled/TheoremsMonolith.agda
```

Stale when: the Schmitty release, Z3 setup action, canonical Agda version, Vehicle Agda-library dependency, or proof-authority boundary changes.
