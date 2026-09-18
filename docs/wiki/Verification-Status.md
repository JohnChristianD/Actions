# Verification Status

Last audited: 2026-09-19.

## Current code head

`a2d1ff089d615adaacfff824c6152737908a7068`

Docs-only commits after this code head update the wiki without changing the proof/CI source.

The current active verification workflow is:

`.github/workflows/guix-composition.yml`

The current theorem entrypoint is:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

## Post-fix workflow

Run `35400839457` is queued for the latest CI repair.

The preceding run `35400721899` failed at container shell startup because the pinned image exposed `guix` but not a standalone `guile` executable. The workflow now launches its Guile shell through `guix shell --pure guile`.

No post-fix run has yet reached the Agda or Mercury lanes, so the current status is **pending**, not green.

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
