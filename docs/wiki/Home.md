# Actions: Canonical Learner, Components, Theorems, and Proof Environment

Last audited: 2026-09-19
Current main head: `d24c59101794ad3b6684889f709e46b5f0c10478` (`Connect finite-cycle exclusion to canonical theorem monolith`).

This repository now has a newer canonical surface than the older coupled-F4 wiki pages.

## Current canonical surface

The active learner is:

- `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`
- `Exotic/ERL/FullCoupled/CanonicalLearnerTheoremsMonolith.agda`
- `Exotic/ERL/FullCoupled/CanonicalClosedLoopInterface.agda`
- `Exotic/ERL/FullCoupled/CanonicalFaithfulGameVariants.agda`

The general theorem substrate remains:

- `GeneralFullCoupledLearnerMonolith.agda`
- `GeneralFullCoupledTheoremsMonolith.agda`

The canonical learner monolith is the source of the concrete learner state and transition. The theorem monolith packages exact composition laws around that source.

## Learner faithfulness

The closed-loop interface now gives explicit typed components:

`ClosedLoopEnv`, `ClosedLoopAgent`, `EpisodeResult`, `EpisodeMetrics`, and `BenchSpec`.

The environment is a typed transition relation `Fin A -> S -> StepResult S`; the agent has explicit action selection and learner-state update; an episode computes return, regret, success, step count, and final state.

The finite environment layer includes exact Toy Maze and FourRooms predicates in `CanonicalFaithfulGameVariants.agda`.

The word "faithful" is deliberately narrow here: these are exact finite structural ports and closed-loop contracts. They do not by themselves prove that the learner reproduces an external simulator, reaches an external benchmark optimum, or is behaviorally equivalent to Gymnax/CleanRL.

## Composed theorem surface

`CanonicalLearnerTheoremsMonolith.agda` now contains:

- `CanonicalAQLoopTheorem`: policy composition, learned-attention composition, shared Watkins signal, GRU/attention coupling, F4 signal coupling, and endogenous Watkins composition.
- `canonicalClockAfter`: exact clock growth under iteration.
- `canonicalAperiodic`: no finite step period returns the state.
- `canonicalNoNontrivialFiniteCycle`: finite-cycle exclusion.
- `CanonicalConnectedCompositionTheorem`: packages the A/Q loop, phase periodicity, clock growth, and finite-cycle exclusion into one connected record.

These laws are source-level equalities, and the current proof bodies are definitionally trivial (`refl`) or direct reuse of already defined canonical lemmas. That is strong evidence about composition of the implemented functions, not a claim about an independent learned system outside this formal model.

## Mercury / Guix / Agda migration

The migration is structurally landed, not CI-complete.

- Haskell theorem/discovery gates were replaced by Mercury.
- Shell-backed Agda and discovery workflows were reduced to legacy `workflow_call` wrappers.
- `.guix/channels.scm` pins Guix channel `version-1.5.0` at commit `ac03c482b1910a1672427beaea07ddcd1d652806`.
- `.guix/manifest.scm` declares Agda 2.7.0.1, Agda standard library 2.3, Mercury 22.01.4, Python 3.11, Guile 3.0, and Git.
- `.github/workflows/guix-composition.yml` is the connected verification entrypoint.

The latest Guix workflow run at this head failed during `actions/checkout@v5` in all four container jobs, before the Agda, Mercury, discovery, or surface lanes executed. Therefore the migration should not be called end-to-end green yet.

## Haskell policy

Haskell has no required role in the current proof or CI architecture.

The migration explicitly removed the Haskell discovery scripts and replaced the theorem/discovery gates with Mercury. The former Agda gate also acquired a source audit that rejects remaining `.hs` files.

This does not assert that Haskell is intrinsically unnecessary as a language. It means the current repository's typed-verifier, theorem, and reproducible-CI roles no longer depend on it.

## Wiki provenance

The hosted `Actions.wiki` repository is not exposed by the current GitHub connection, so this directory is the authoritative in-repository wiki mirror.

Older pages that describe `CanonicalCoupledF4Learner.agda` as the current canonical target are historical references and have been rewritten here around the current monolith surface.
