# Verification Status

Last audited: 2026-09-19.

## Current code head

`7c2388a76e99dff571964d1f1e27cd78be1c85d6`

Docs-only commits after this code head update the wiki without changing the proof/CI source.

The current active verification workflow is:

`.github/workflows/guix-composition.yml`

The current theorem entrypoint is:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

## Current workflow

Latest verification run: `35403637915` at `7c2388a76e99dff571964d1f1e27cd78be1c85d6`.

The four jobs are currently queued. No Agda or Mercury result has been observed yet, so this source state remains pending rather than green.

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


## GESMR endogenous discovery

Mercury now includes MR15_GA, GESMR_GA, Open_ES, HillClimbing, PSO, DifferentialEvolution, and an MCTX candidate in the finite property grammar. The accepted candidate for the Watkins/F4-L2/GRU grouped-mutation requirement is GESMR_GA.

The Agda monolith contains finiteGESMRWatkinsF4L2GRUCompositionTheorem and finite-gesmr-watkins-f4-l2-gru-composition-theorem.