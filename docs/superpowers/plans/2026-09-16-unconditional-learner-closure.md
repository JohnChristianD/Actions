# Unconditional Canonical Learner Closure Implementation Plan

Authority: `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda` plus the synchronized replication wiki.

## Closed theorem surface

- [x] Environment-agnostic Watkins/LCB/sparsemax/negative-q-log/attention/Walsh/hard-sign-Möbius-GRU/F4-L2/NormPair learner.
- [x] Persistent-GRU quotient and transition-action endomorphism monoid.
- [x] Associative GRU and Möbius-labelled scan laws.
- [x] Exact H4 Int8 Gram law `H4 H4ᵀ = 4I (mod 256)`.
- [x] Power-of-four width witness.
- [x] Full stored Int8 accounting including F4 and NormPair: 23 scalar coordinates.
- [x] Width-`d` bookkeeping: `d + 22` stored Int8 coordinates under scalar persistent layout.
- [x] NormPair/F4/L2 hard-sparsity structural invariance theorem.
- [x] Exact Nat rank `V = clock`, unit increment, fixed-point and finite-cycle exclusion.

## Width and algebra

- [x] Replication default `d = 64`.
- [x] `FiniteParameterCompleteness.agda` proves `64 = 4^3` and finite function-table completeness.
- [x] Effective theorem algebra documented below ring level: finite data, Nat arithmetic, equality/negation, products, and endomorphism composition.
- [x] Current source retained on the eight direct standard-library imports it actually uses.

## Environment replication

- [x] Finite executable ports for Jumanji Knapsack, Maze, LevelBasedForaging.
- [x] Finite executable ports for Gymnax MetaMaze, FourRooms, Pong, MemoryChain, DiscountingChain, CartPole, Bernoulli Bandit.
- [x] Finite executable Pobax RockSample projection.
- [x] Exact fixed Jumanji Toy Maze connectivity predicate.
- [x] Exact Gymnax FourRooms 13x13 connectivity predicate.
- [x] Explicitly distinguish deterministic finite projections from upstream stochastic/continuous numerical implementations.

## Learner execution

- [x] `CanonicalLearnerGameExecution_test.agda` injects every port reward through an explicit `Fin 256` adapter.
- [x] Canonical learner step executes after every reward injection.
- [x] Clock-progress proof is checked for every listed environment.
- [ ] Empirical learning quality/convergence remains intentionally unclaimed because the current theorem surface has no statistical or continuous-performance metric.

## CNN/log-pyramid preservation

- [x] `CNNLogPyramid64` explicit 64-index representation.
- [x] `cnnToAttention` decoder.
- [x] GRU-input preservation under equal decoded attention state.
- [x] Commuting theorem from CNN pyramid representation into the existing `canonicalGRUStep`.
- [ ] A theorem for arbitrary CNN convolution/pooling architectures remains outside the current source because no CNN layer algebra is defined.

## GameTheory and retired branches

- [x] `GameTheory.agda` moved to the canonical eight-import surface and removed `efficient_chad.Int8` dependency.
- [x] Current repository search finds no active `MR15Reachability`, `OpenESDyadic`, or `NoisyNetCoupled` references on the canonical branch.
- [x] Current branch inventory has no active remote refs named Noisy Nets, OpenES, or MR15.

## Synchronization

- [x] Forbidden-theorem scanner covers learner, game ports, faithful map variants, completeness, CNN preservation, execution regression, GameTheory, and generated report.
- [x] Haskell theorem generator checks all required surfaces and runs Agda safe checks.
- [x] Workflow compiles all maintained Agda surfaces before generation.
- [x] Replication wiki synchronized to d64, finite functional completeness, game ports, CNN preservation, state accounting, and exact Nat rank.
- [x] Main-branch pushes, PRs, schedules, and manual workflow dispatch use the same canonical gate, so merges automatically re-enter the synchronization/verification path.

## Acceptance

The active PR is `#36`, branch `agda-theorem-first-monolith-20260916`. The previous authoritative gate failed only after the canonical clock proof and before the new environment surface existed. A failed-job rerun has now been requested against the current PR checkout. Do not mark the branch green until canonical Agda, all port/faithful-map surfaces, completeness, CNN preservation, learner execution regression, generator, redundancy audit, and generated report all pass on the current PR head.
