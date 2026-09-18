# Verification Status

Last audited: 2026-09-19.

## Current code head

Latest code/proof source head:
`16a1714bb3e2ef5397d75384ec494165bfc2e4db`

The current active verification workflow is:

`.github/workflows/guix-composition.yml`

The current theorem entrypoint is:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

## Current workflow

Latest verification run for the current code changes:
`35405054668`

The immediately preceding run `35404988310` failed in the container checkout step because the Guix daemon socket was absent, before the Agda or Mercury lanes could execute. The workflow now starts `guix-daemon --disable-chroot` inside the pinned CI container and authorizes the standard Guix substitute keys before checkout.

Run `35405054668` is currently queued/pending. No Agda or Mercury success/failure result has been observed yet, so this source state remains pending rather than green.

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
## TSTS + PVS + GESMR status

Mercury now runs `tsts_pvs_composition_discovery.m`. Its semantic gate includes TSTS tree selection, PVS exact recheck, the canonical learner evaluator, endogenous F4/L2 -> Watkins -> GRU/F4 coupling, preservation invariants, adaptive/grouped mutation control, and the external TSTS finite-time-regret property.

The selected finite candidate is `TSTS_PVS_GESMR_GA`.

Agda contains `FiniteTSTSPVSGESMRConnectedTheorem` plus the test module `Exotic/ERL/FullCoupled/TSTS_PVS_GESMR_test.agda`.

The theorem is a repository-local finite composition certificate. It does not claim that the complete probabilistic TSTS runtime or a full PVS chess-style engine has been reproduced.

## EvoSAX challenger portfolio

The finite Mercury portfolio grammar now explicitly includes RandomSearch, HillClimbing, SimpleES, SimpleGA, OpenES, MR15-GA, SAMR-GA, GESMR-GA, PGPE, SNES, CMA-ES, DifferentialEvolution, and ParticleSwarm.

These remain proof-friendly finite analogues and challenge kernels. Agda remains authoritative for accepted learner semantics.

## Container boundary

Hadolint is not used as a runtime/containerization layer. The existing digest-pinned Guix job container plus Guix time-machine already supplies the isolation and reproducibility boundary. A Haskell Dockerfile linter would be appropriate only for linting Dockerfiles, not for wrapping the Guix environment.
