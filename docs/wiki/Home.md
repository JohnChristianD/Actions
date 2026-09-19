# Actions: Canonical Learner, Novel Theorem Discovery, and Proof Environment

Last audited: 2026-09-19.

Current code head is tracked directly in Git; this branch is not declared CI-green until the new Mercury/Agda discovery lane completes.

## Single active theorem source

The canonical theorem entrypoint is:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

It owns the canonical learner composition laws, phase periodicity, clock growth, finite-cycle exclusion, and the existing TSTS/attention connected theorems. The discovery layer is separate and searches for additional unincluded learner laws.

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

Mercury now owns the finite novel-theorem candidate engine. Agda remains authoritative for exact learner semantics and theorem acceptance. The outer search is a learner-discovery mechanism, not a self-certifying proof layer.

The canonical source audit rejects Haskell, Python, JavaScript/TypeScript, JVM-family source, Elm, and PureScript source files.

The workflow uses a digest-pinned Guix container, boots the Guix daemon inside each job, performs source checkout with Guix-provided Git, and then enters the pinned Guix environment.

## Symbolic learner theorem search

The active search target is a typed symbolic theorem program over actual learner transformations. Mercury enumerates a small basis grammar, quotients derived candidates, removes declarations already represented in the theorem monolith, and generates concrete Agda theorem declarations.

The current basis uses NormPair replacement and the period-4 clock transformation with target-invariance and full-step-equivariance relations. Iterate-equivalence candidates are used as quotienting information and are not emitted when subsumed by the stronger one-step relation.

The loop is:

`symbolic theorem -> equivalence quotient -> source novelty guard -> Agda proposition -> agda --safe`

PVS, JAxtar/A*/Q*, evolutionary-population proposal layers, and the old TSTS discovery generator are pruned from the canonical search path.

## Verification target

The program/tree-search layer is used to propose, select, or refine learner-side candidates. Its purpose is to explore learner consistency by sending learner candidates and observations into the exact formal path. It is not used to prove its own search algorithm self-consistent.

## Discovery status

The existing `FiniteTSTSEndogenousConnectedTheorem` remains part of the theorem surface, but discovery no longer searches for TSTS composition itself.

The current novel basis is:

- Watkins-target invariance under NormPair replacement;
- Watkins-target invariance under the period-4 clock transformation;
- canonical full-step equivariance under NormPair replacement;
- canonical full-step equivariance under the period-4 clock transformation.

These candidates are generated into a transient Agda module and must pass `agda --safe` before they can be considered verified. They are not auto-promoted into the canonical theorem monolith.
## CleanRL / LeanRL relationship

The architecture intentionally borrows the useful single-file property: the algorithm/theorem variant has one obvious source of truth.

It does not attempt to reproduce CleanRL or LeanRL as a software architecture. Agda contributes proof checking, Mercury contributes typed deterministic verification, and Guix contributes reproducible dependency isolation.

## Wiki status

The in-repository `docs/wiki/` tree is the maintained documentation surface.
