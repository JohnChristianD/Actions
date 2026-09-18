# Verification Status

Last audited: 2026-09-19.

## Current code head

Current code/proof source is moving with the TSTS-only refactor. The most recent code/CI repair commit currently visible is:

`0b376ed889963971986bc58f716cb502de9bf58f`

The current theorem entrypoint is:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

## Current workflow

Latest verification run for the current code changes:
`35405803150`

The immediately preceding run `35404988310` failed in the container checkout step because the Guix daemon socket was absent, before the Agda or Mercury lanes could execute. The workflow now starts `guix-daemon --disable-chroot` inside the pinned CI container and authorizes the standard Guix substitute keys before checkout.

The current repair commit hardens the pinned Guix container with `--security-opt seccomp=unconfined`, after run `35405803150` failed in `guix shell` because the `setPersonality` syscall was blocked by the container's seccomp profile. A new verification run is required before the theorem can be called green.

## Active search architecture

The active outer search is now TSTS-only.

Retired from the canonical discovery path:

- JAxtar A*/Q* graph-search adapter.
- PVS recheck layer.
- OpenES/GESMR/MR15/SAMR/EvoSAX population search layer.

Mercury now runs `.ci/discovery/tsts_endogenous_discovery.m` and emits `.ci/discovery/tsts-endogenous-composition-candidate.json`.

Agda tests now live in:

`Exotic/ERL/FullCoupled/TSTS_Connected_test.agda`

The canonical theorem is `FiniteTSTSEndogenousConnectedTheorem`.

## Verification status

The latest repair run visible during this audit is still pending. The earlier run failed before any Agda or Mercury execution because the Guix container had no running Guix daemon. The workflow now boots the daemon inside the digest-pinned container before performing the Guix-native checkout.

No current run is being called green until the Agda and Mercury lanes actually execute and succeed.

## Endogenous theorem status

The new theorem connects:

TSTS posterior witness -> selected learner branch -> exact canonical learner -> endogenous Watkins target -> TSTS posterior update

while the same target drives both the GRU and F4 tell paths.

The F4/L2 case explicitly expands the target through thetaQ, probe, L2 correction, attention feedback, GRU feedback, and q-log feedback. NormPair and persistent-GRU preservation are retained.

The proof is a repository-local finite semantic specialization. It does not inherit the external TSTS Bayesian regret theorem automatically.



## Intrinsic learner theorem

Added `FiniteAttentionWatkinsGRUF4MediatorTheorem` and
`Attention_Mediator_Connected_test.agda`.

This theorem is independent of TSTS, EA, program search, PVS, and JAxtar. It formalizes an attention-mediated separation:

attention replacement -> policy/count/Q-log invariance -> endogenous Watkins target -> shared GRU and F4 consumption

while preserving NormPair and persistent-GRU observables through the canonical full step.

The prior verification run for this addition was `35405803150`, which failed at the Guix-native checkout step before Agda or Mercury executed. The theorem and direct test therefore remain formally unverified by CI until the hardened workflow completes.
