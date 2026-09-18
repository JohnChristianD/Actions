# Verification Status

Last audited: 2026-09-19.

## Current code head

`bb677317bd435dd4d23799cae4fbfb9878845ea0`

Docs-only commits after this code head update the wiki without changing the proof/CI source.

The current active verification workflow is:

`.github/workflows/guix-composition.yml`

The current theorem entrypoint is:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

## Current workflow

Latest verification run: `35402942175` at `bb677317bd435dd4d23799cae4fbfb9878845ea0`.

At the latest status read, all four jobs are in progress during container initialization. No lane has yet reported a proof failure or success.

The preceding checkout failure was caused by cloning directly into the pre-created GitHub Actions workspace. The workflow now initializes the workspace as a Git repository, adds the origin, fetches the exact commit, and checks it out. The workflow uses the container's native `sh` shell and keeps Guix pinning outside the pure Guile environment.

## New composition discovery

Mercury now runs `formal_openes_composition_discovery.m`, which searches a finite variation/property grammar and selects `Open_ES` for the required two-sided probe, antithetic estimator, F4/L2 tell, canonical learner evaluator, norm-pair preservation, and persistent-GRU preservation obligations.

The selected candidate is implemented in `TheoremsMonolith.agda` as `finite-openES-canonical-composition-theorem`.

This is a finite symbolic EvoSAX/OpenAI-ES specialization, not a claim of floating-point or JAX-level numerical equivalence.

## Structural repairs now present

- Python discovery implementation removed.
- Python removed from the pinned Guix manifest.
- Mercury now emits the finite A/Q discovery report directly.
- Only `.github/workflows/guix-composition.yml` remains.
- Old Agda/F4/composite/symbolic-discovery workflows removed.
- Old canonical theorem module removed.
- `TheoremsMonolith.agda` is the single canonical theorem discovery entrypoint.
- Mercury A/Q certificate folded into the theorem monolith.
- Guile-native Git checkout replaces `actions/checkout` inside the Guix container.
- The Guix workflow shell launches Guile through the pinned Guix environment.
- Discovery artifact checking no longer depends on `actions/upload-artifact`.
- Surface audit rejects Haskell, Python, JS/TS, JVM-family, Elm, PureScript, shell, and Windows script source.

## JAxtar A/Q status

Mercury now owns the executable finite A/Q graph verification and JSON report.

Agda owns the corresponding typed certificate and composition theorem in `TheoremsMonolith.agda`.

This is a port of the finite A/Q graph/certificate boundary, not a full JAX/JAxtar solver reimplementation.

## Verification rule

A theorem is called verified only after the current Guix/Agda `--safe` lane has actually checked its owning module.

The queued run is therefore recorded as pending, not green.
