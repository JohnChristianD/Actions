# Actions: Canonical Learner, TSTS Endogenous Theorem, and Proof Environment

Last audited: 2026-09-19.

Current code head: `dc4d58b00f23970d9652166a718437a4943f4d05`.

## Single active theorem source

The canonical theorem entrypoint is:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

It owns the canonical learner composition laws, phase periodicity, clock growth, finite-cycle exclusion, and the active TSTS-only endogenous connected theorem.

The older canonical theorem modules remain retired. The generic theorem monolith remains only as legacy/general infrastructure and is not the discovery entrypoint.

## Current learner components

The active implementation is:

- `CanonicalLearnerMonolith.agda`
- `CanonicalClosedLoopInterface.agda`
- `CanonicalGamePorts.agda`
- `CanonicalFaithfulGameVariants.agda`

The learner state and one-step transition live in the learner monolith. The theorem monolith proves and packages laws over that implementation.

## Learner faithfulness

The closed-loop interface gives typed:

`ClosedLoopEnv`, `ClosedLoopAgent`, `EpisodeResult`, `EpisodeMetrics`, and `BenchSpec`.

Finite Toy Maze and FourRooms variants are represented directly in Agda.

“Faithful” is deliberately limited to the formal interface and exact finite predicates. It does not establish behavioral equivalence with an external simulator.

## Mercury / Guix / Agda

The executable formal-RL path is:

`Guix -> Guile orchestration -> Agda --safe + Mercury`

Mercury now owns the small finite TSTS composition boundary. Agda remains authoritative for exact learner semantics and theorem acceptance.

The canonical source audit rejects Haskell, Python, JavaScript/TypeScript, JVM-family source, Elm, and PureScript source files.

The workflow uses a digest-pinned Guix container, boots the Guix daemon inside each job, performs source checkout with Guix-provided Git, and then enters the pinned Guix environment.

## TSTS-only meta-search

The active outer search is a finite TSTS-style tree over endogenous learner-composition branches.

The loop is:

`posterior sample -> branch -> exact learner probe -> endogenous Watkins reward -> posterior update`

The same Watkins target also feeds the GRU and F4 tell paths.

PVS, JAxtar/A*/Q* graph search, and evolutionary-population proposal layers have been removed from the canonical discovery path because they duplicate or introduce orthogonal search state without strengthening this endogenous connection.

## Active theorem

`FiniteTSTSEndogenousConnectedTheorem`

The theorem connects:

`TSTS sample -> endogenous learner probe -> canonical Watkins target -> TSTS posterior update -> GRU/F4 tell`

and proves preservation of the `NormPair` observable and persistent-GRU quotient.

The F4/L2 case explicitly exposes the path through `thetaQ`, the probe, L2 correction, attention feedback, GRU feedback, and q-log feedback.

This is a finite semantic specialization. It is not a numerical reproduction of the external TSTS implementation and does not inherit the external Bayesian regret theorem automatically.

## CleanRL / LeanRL relationship

The architecture intentionally borrows the useful single-file property: the algorithm/theorem variant has one obvious source of truth.

It does not attempt to reproduce CleanRL or LeanRL as a software architecture. Agda contributes proof checking, Mercury contributes typed deterministic verification, and Guix contributes reproducible dependency isolation.

## Wiki status

The in-repository `docs/wiki/` tree is the maintained documentation surface.
