# Actions: Canonical Learner, Theorem Monolith, and Proof Environment

Last audited: 2026-09-19.

Current code head: `bb677317bd435dd4d23799cae4fbfb9878845ea0`.

## Single active theorem source

The current canonical theorem entrypoint is:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

It owns the current A/Q composition theorem, connected composition theorem, phase periodicity, clock growth, finite-cycle exclusion, and the typed Mercury/JAxtar A/Q certificate.

The older `CanonicalLearnerTheoremsMonolith.agda` and `CanonicalCoupledCompositionTheorems.agda` surfaces have been retired.

The generic `GeneralFullCoupledTheoremsMonolith.agda` remains only as a legacy/general theorem substrate for noncanonical certificate machinery. It is not the discovery entrypoint.

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

"Faithful" is deliberately limited to the formal interface and exact finite predicates. It does not establish behavioral equivalence with an external Gymnax, CleanRL, or simulator implementation.

## Mercury / Guix / Agda

The executable formal-RL path is now:

`Guix -> Guile orchestration -> Agda --safe + Mercury`

The finite A/Q discovery path is Mercury-native. Python is no longer in the Guix manifest or discovery workflow.

The repository source audit rejects Haskell, Python, JavaScript/TypeScript, JVM-family source, Elm, and PureScript source files from the canonical surface.

The workflow also avoids JavaScript GitHub actions inside the Guix container. Source checkout is performed by Guile invoking Guix-provided Git. The workflow keeps source checkout and Guix pinning in the outer shell, then enters the pinned Guile environment. The latest repair run is pending; the previously observed Guile-checkout failure is not being treated as green.

## JAxtar A/Q boundary

The repository now contains a Mercury typed finite graph model and an Agda proof certificate for the A/Q path:

`LCB -> sparsemax -> attention`

`attention -> Walsh-Hadamard -> finite phase -> recurrent signal`

`sparsemax -> q=2 negative bias -> Watkins`

This is a Mercury/Agda formal port of the A/Q graph and certificate boundary.

It is not a full port of the external JAxtar JAX search engine. The external JAxtar project is a JAX-native parallel A*/Q* solver with neural-heuristic integration; this repository keeps only the exact finite A/Q graph semantics needed by the proof/discovery surface. The new Open_ES theorem is a meta-optimizer composition, not an A*/Q* solver implementation.

## Meta-search

`docs/wiki/Meta-Search.md` defines the formal EvoSAX-family Mercury search layer, the JAxtar A*/Q graph-search boundary, the Lion-style program-discovery loop, and the manual parameter/import boundary.

## Language policy

The active source languages are intentionally small:

- Agda for kernel-checked semantics and theorems;
- Mercury for typed executable verification and finite discovery;
- Guile Scheme through Guix for reproducible orchestration.

No JVM language, Elm, PureScript, JavaScript, or TypeScript layer is needed by the current formal architecture.

The GitHub Actions platform itself can run JavaScript actions, but the canonical Guix workflow no longer relies on them inside its job container.

## CleanRL / LeanRL relationship

The architecture intentionally borrows the useful single-file property: the algorithm/theorem variant has one obvious source of truth.

It does not attempt to reproduce CleanRL or LeanRL as a software architecture:

- CleanRL emphasizes single-file RL implementations, explicit algorithm details, reproducibility, and benchmarking.
- LeanRL keeps that single-file shape while optimizing selected implementations with PyTorch compilation features.
- Agda contributes proof checking, not RL training.
- Mercury contributes typed deterministic verification, not GPU RL execution.
- Guix contributes reproducible dependency isolation, not the algorithm's internal style.

So the repository is **CleanRL-like in source-of-truth discipline**, not a literal implementation of the CleanRL/LeanRL runtime philosophy.

## Wiki status

The in-repository `docs/wiki/` tree is the maintained documentation surface available through the current repository connection.
