# Verification Status

Last audited: 2026-09-19.

## Current architecture

Canonical theorem entrypoint:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

Canonical implementation entrypoint:

`Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

Canonical CI entrypoint:

`.github/workflows/guix-composition.yml`

The old workflow family and the superseded canonical theorem module have been pruned.

## Latest historical failure

The previous Guix run `35397895896` failed at `actions/checkout@v5` inside the Guix container.

That specific failure mode has been removed from the workflow: the current workflow performs source checkout with Guile invoking Guix-provided Git, then loads the pinned CI driver.

No current post-fix Guix run has yet established a green result, so the repair is structurally applied but not yet empirically closed.

## Current migration

The intended verification path is:

`Guix channel pin -> pure manifest -> Agda --safe + Mercury`

Python finite discovery is removed.

The current surface audit rejects:

- Haskell;
- Python;
- JavaScript / TypeScript;
- JVM-family source;
- Elm;
- PureScript;
- shell and Windows script files.

## JAxtar A/Q

The A/Q graph is now represented twice in different proof roles:

- Mercury performs the executable finite path check and writes the deterministic discovery report.
- Agda `TheoremsMonolith.agda` contains the corresponding typed certificate and connected composition theorem.

This is a Mercury + Guix + Agda port of the **A/Q graph/certificate boundary**.

It is not a full reimplementation of JAxtar's JAX parallel A*/Q* engine.

## Interpretation rule

The theorem monolith is the current source of truth for canonical theorem discovery.

A theorem is called verified only after the current Guix/Agda `--safe` job actually reaches and checks it.
