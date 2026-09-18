# Verification Status

Last audited: 2026-09-19.

## Current code head

`3083a82ccb6bbcb1089f6718199c89b6e31b6da1`

The current active verification workflow is:

`.github/workflows/guix-composition.yml`

The current theorem entrypoint is:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

## Post-fix workflow

Run `35400721899` is currently in progress.

At the latest inspection, all four jobs had initialized successfully and were still in container initialization, before Guile-native checkout or the proof lanes executed.

Therefore the post-fix architecture is not yet empirically green. The old failure at JavaScript checkout is no longer the current workflow shape.

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
- Discovery artifact checking no longer depends on `actions/upload-artifact`.
- Surface audit rejects Haskell, Python, JS/TS, JVM-family, Elm, PureScript, shell, and Windows script source.

## JAxtar A/Q status

Mercury now owns the executable finite A/Q graph verification and JSON report.

Agda owns the corresponding typed certificate and composition theorem in `TheoremsMonolith.agda`.

This is a port of the finite A/Q graph/certificate boundary, not a full JAX/JAxtar solver reimplementation.

## Verification rule

A theorem is called verified only after the current Guix/Agda `--safe` lane has actually checked its owning module.

The current in-progress run is therefore recorded as pending, not green.
