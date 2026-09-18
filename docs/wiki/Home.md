# Actions: Canonical Learner, TSTS Endogenous Theorem, and Proof Environment

Last audited: 2026-09-19.

Current code head: `568f536787af6e74702b05b5b9126d7868d3419f`.

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

Mercury now owns the small finite TSTS composition boundary. Agda remains authoritative for exact learner semantics and theorem acceptance. The outer search is a learner-discovery mechanism, not a self-certifying proof layer.

The canonical source audit rejects Haskell, Python, JavaScript/TypeScript, JVM-family source, Elm, and PureScript source files.

The workflow uses a digest-pinned Guix container, boots the Guix daemon inside each job, performs source checkout with Guix-provided Git, and then enters the pinned Guix environment.

## Symbolic learner theorem search

The active search target is a typed symbolic program over actual learner transformations. The current finite search enumerates attention, NormPair, and optimizer replacement compositions and generates concrete Agda theorem declarations for them.

The loop is:

`symbolic composition -> Agda proposition -> generated proof -> agda --safe`

The discovery metric is deliberately left outside this semantic invariant. PVS, JAxtar/A*/Q* graph search, and evolutionary-population proposal layers remain pruned from the canonical path.

## Verification target

The program/tree-search layer is used to propose, select, or refine learner-side candidates. Its purpose is to explore learner consistency by sending learner candidates and observations into the exact formal path. It is not used to prove its own search algorithm self-consistent.

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
