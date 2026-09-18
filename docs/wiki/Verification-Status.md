# Verification Status

Last audited: 2026-09-19.

## Current head

`d24c59101794ad3b6684889f709e46b5f0c10478`

Commit:

`Connect finite-cycle exclusion to canonical theorem monolith`

## What is structurally in place

The current main branch contains:

- canonical learner monolith;
- canonical learner theorem monolith;
- canonical closed-loop interface;
- exact finite Toy Maze and FourRooms variants;
- Mercury theorem/discovery/verifier sources;
- pinned Guix channel and manifest;
- Guix-native connected CI;
- legacy Agda/discovery workflows reduced to `workflow_call` wrappers.

## Latest CI result

The latest `Guix connected composition verification` run is:

run `35397895896`

Result: **failure**.

All four jobs failed at `actions/checkout@v5` inside the Guix container before the lane body ran:

- Guix / Agda --safe connected theorem surface
- Guix / Mercury connected theorem and verifier lane
- Guix / automated finite discovery
- Guix / no Haskell, Cabal, shell, or CMD surface

Therefore the current head has not yet received an end-to-end green Guix verification.

The failure is an infrastructure/entrypoint failure at checkout. The later Agda and Mercury commands were skipped, so this run provides no evidence about their current execution inside the pinned Guix environment.

## Agda theorem closure

`CanonicalLearnerTheoremsMonolith.agda` now contains the connected composition record and the finite-cycle exclusion.

Its theorem bodies are source-level equalities and direct reuse of canonical lemmas. This is enough to type-check the declarations when Agda reaches the module, but the current Guix run did not reach them.

The previous wiki's `coupled-f4-closure.yml` status is historical. It is not the current CI status for main.

## Mercury migration status

The old Haskell discovery/theorem gates were replaced by Mercury.

Current Mercury roles:

- forbidden-theorem scanning;
- learner-module audit;
- component audit;
- typed A/Q discovery;
- involution verification;
- rational oracle.

The Mercury verifier sources are present on main.

The current Guix failure means these lanes have not yet been revalidated at `d24c591`.

## Haskell status

No current proof design depends on Haskell.

The migration commits removed the Haskell discovery scripts, replaced the Haskell CI calls with Mercury, and added a policy check for lingering `.hs` sources.

Therefore Haskell is not part of the intended current toolchain for this repository.

That is a repository architecture statement, not a statement that Haskell has no useful role elsewhere.

## Reproducibility status

Guix is pinned by:

- `.guix/channels.scm`
- `.guix/manifest.scm`
- the digest-pinned Guix container image in `.github/workflows/guix-composition.yml`.

The intended CI path is now Guix/Guile-driven rather than shell-script-driven.

The remaining closure task is operational: make checkout/entry into the Guix container succeed, then rerun the Agda, Mercury, discovery, and surface lanes and record their actual results here.

## Interpretation rule

A declaration in a theorem record is counted as verified only after its owning Agda module has actually passed the current Safe Agda lane.

A certificate field is not treated as a proved property merely because a record type names it.

This page separates source-level theorem completeness from current CI execution status.
