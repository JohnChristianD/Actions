# Verification Status

Last audited: 2026-09-19.

## Current code head

Current code/proof source is moving with the TSTS-only refactor. The most recent code/CI repair commit currently visible is:

`e5dae8eac5d76ecae6fff53e35de4edd9a934449`

The current theorem entrypoint is:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

## Current workflow

Latest verification run for the current code changes:
`35405054668`

The immediately preceding run `35404988310` failed in the container checkout step because the Guix daemon socket was absent, before the Agda or Mercury lanes could execute. The workflow now starts `guix-daemon --disable-chroot` inside the pinned CI container and authorizes the standard Guix substitute keys before checkout.

Run `35405054668` is currently queued/pending. No Agda or Mercury success/failure result has been observed yet, so this source state remains pending rather than green.

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

