# General Action Closed-Loop Bench Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the two-action policy bottleneck with a general finite-action learner interface, then execute the same learner end-to-end against modular finite game ports with exact return/regret/success metrics and Munchausen ablation.

**Architecture:** `CanonicalLearnerMonolith.agda` remains the only learner source and contains all learner definitions/proofs needed for compilation. `CanonicalGamePorts.agda` remains independent and environment-specific. `GeneralClosedLoopBench.agda` instantiates the generic action interface without importing game code into the monolith.

**Tech Stack:** Agda `--safe`, existing standard-library imports already used by the monolith, deterministic finite game projections, GitHub Actions.

**Spec:** This repository task request.

## Global Constraints

- Default hidden/representation width is `d = 64`.
- Learner monolith must remain self-contained and environment-agnostic.
- Game environments remain external modular files.
- No holes, postulates, placeholders, or new logical assumptions.
- Prefer existing direct imports; add a standard-library import only when a concrete proof requires it.
- Sparsemax must support arbitrary finite action count `A`; no hard-coded 2-action policy remains on the canonical path.
- Bench must record exact return, regret, success, and steps.
- Munchausen and no-Munchausen runs differ by one explicit learner mode only.
- No statistical aggregation is required in Agda; exact deterministic witness metrics are sufficient.

---

### Task 1: General finite-action sparsemax

**Files:**
- Modify: `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`
- Test: `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda`

- [ ] Introduce `QVec A = Fin A -> Int8` and finite action enumeration without a 2-action special case.
- [ ] Define an exact finite-temperature sparsemax rational weight using score sums and cross-multiplied threshold tests, avoiding division in the proof kernel.
- [ ] Prove support nonnegativity, simplex-sum scaling, argmax preservation, and `A=2` compatibility.
- [ ] Make the canonical action selector consume the generic `QVec A` path.
- [ ] Add tests at `A = 2`, `A = 4`, and `A = 64`.

### Task 2: Full learner state composition

**Files:**
- Modify: `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

- [ ] Preserve Watkins, LCB, negative finite q-log, sparsemax attention, Walsh/H4, hard-sign gate, Mobius boundary, GRU persistence, F4 optimizer, NormPair, and coupled L2.
- [ ] Generalize action-dependent state updates over `Fin A`.
- [ ] Prove transition preservation of the GRU equivalence class under arbitrary actions.
- [ ] Prove exact clock rank and no-finite-cycle theorem for the full generalized step.

### Task 3: Closed-loop learner/environment interface

**Files:**
- Modify: `Exotic/ERL/FullCoupled/GeneralClosedLoopBench.agda`
- Test: `Exotic/ERL/FullCoupled/GeneralClosedLoopBench_test.agda`

- [ ] Define the environment interface as `Fin A -> State -> StepResult State`.
- [ ] Select actions exclusively from `canonicalPolicyA`.
- [ ] Inject observed reward into the learner step and feed next learner state back into the selector.
- [ ] Record exact return, reference return, regret, success, and steps.
- [ ] Instantiate all maintained ports: CartPole, Bernoulli bandit, MetaMaze, FourRooms, Maze, Knapsack, LevelBasedForaging, Pong-misc, MemoryChain, DiscountingChain, RockSample.

### Task 4: Munchausen ablation

**Files:**
- Modify: `Exotic/ERL/FullCoupled/GeneralClosedLoopBench.agda`
- Test: `Exotic/ERL/FullCoupled/GeneralClosedLoopBench_test.agda`

- [ ] Define `NoMunchausen` and `Munchausen` kernels differing only in the finite q-log shaping term.
- [ ] Run identical initial state, horizon, environment transition, action decoder, and optimizer settings under both modes.
- [ ] Record paired exact metrics for every environment.
- [ ] Prove the initial-state structural identity of all non-Munchausen components.

### Task 5: CNN/representation theorem boundary

**Files:**
- Modify: `Exotic/ERL/FullCoupled/CNNLogPyramidPreservation.agda`

- [ ] Define an explicit finite representation equivalence relation.
- [ ] Prove transition congruence through the decoder-induced learner input map.
- [ ] Do not claim a CNN component is already part of the learner.
- [ ] Define the minimal external CNN interface needed for an explicit simulation theorem.

### Task 6: Synchronization and CI

**Files:**
- Modify: `.github/workflows/agda.yml`
- Modify: `.ci/check-agda-safe-surface.py`
- Modify: `.ci/discovery/ExplorationTheoremGenerator.hs`
- Modify: `docs/GENERAL_CLOSED_LOOP_BENCH.md`
- Modify: `docs/THEOREM_FIRST_REPLICATION_WIKI.md`

- [ ] Make the generalized canonical monolith and game bench mandatory CI targets.
- [ ] Reject residual 2-action-only canonical policy definitions.
- [ ] Reject holes/postulates/placeholders.
- [ ] Keep the monolith free of environment imports.
- [ ] Keep post-merge synchronization automatic through the existing repository workflow surface.

---

## Completion Evidence Matrix

| Requirement | Evidence | Status |
|---|---|---|
| General-action sparsemax | Agda typecheck + `A=2/4/64` tests | pending |
| Full learner transition | Agda typecheck + clock theorem | pending |
| Closed-loop interface | Bench module + exact witness metrics | pending |
| Return/regret/success | `LoopResult` witness fields | pending |
| Munchausen ceteris-paribus | Paired mode definitions + identical kernel proof | pending |
| CNN transition congruence | explicit relation + transition theorem | pending |
| No learner->environment import | CI dependency scan | pending |
| No holes/postulates/placeholders | CI forbidden-surface scan | pending |
