# General Monolith Import/Search/Prune Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Expand the formal substrate for automated theorem discovery, keep the theorem layer in one monolith separate from the learner monolith, prove arbitrary finite recurrence depth, and remove the misleading regret metric.

**Architecture:** Keep `GeneralFullCoupledLearnerMonolith.agda` as the learner kernel and `GeneralFullCoupledTheoremsMonolith.agda` as the sole generalized theorem source. Fold the current theorem-closure wrappers into that theorem monolith, add useful standard-library Nat algebra, and preserve a future migration path from the local list/insertion-sort carrier to stdlib sorting with a `DecTotalOrder` without pretending that migration is already kernel-verified.

**Tech Stack:** Agda `--safe`, Agda standard library `Data.Nat.Properties`, `Relation.Binary`, stdlib sorting/permutation APIs where introduced, GitHub Actions, existing Haskell theorem-surface discovery.

**Spec:** User request in conversation dated 2026-09-17.

## Global Constraints

- The generalized learner monolith and generalized theorem monolith remain separate files.
- Generalized theorem statements belong in `GeneralFullCoupledTheoremsMonolith.agda`, not in a parallel closure file.
- No proof holes, postulates, or conditional certificates may be relabeled as completed theorems.
- Search-oriented imports are additive when they enlarge useful algebraic proof vocabulary.
- Regret is removed from the active generalized closed-loop benchmark surface.
- No fresh CI success claim without an observed run.

---

### Task 1: Restore useful Nat algebra vocabulary

**Files:**
- Modify: `Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremsMonolith.agda`

**Interfaces:**
- Consumes: existing learner clock recurrence.
- Produces: a theorem using `Data.Nat.Properties` to expose the monotone/unbounded clock algebra cleanly.

- [ ] Add `Data.Nat.Properties` only where a new theorem consumes its algebraic lemmas.
- [ ] Add a clock monotonicity theorem derived from `iterateLearner-clock` and standard Nat order algebra.
- [ ] Keep the theorem kernel-safe and constructive.

### Task 2: Fold the generalized theorem closure into the theorem monolith

**Files:**
- Modify: `Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremsMonolith.agda`
- Delete: `Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremClosure.agda`
- Modify: `.github/workflows/agda.yml`

**Interfaces:**
- Consumes: every theorem already present in `GeneralFullCoupledTheoremClosure.agda`.
- Produces: one generalized theorem source with no theorem-closure companion.

- [ ] Copy each closure theorem into the theorem monolith without weakening statements.
- [ ] Compile the new definitions conceptually against existing names and avoid accidental collisions.
- [ ] Remove the now-redundant closure CI gate.
- [ ] Delete the closure file after the monolith contains its theorem surface.

### Task 3: Prove arbitrary finite nonlinear recurrence depth

**Files:**
- Modify: `Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremsMonolith.agda`

**Interfaces:**
- Consumes: `traceGRU`, `traceIterate`, `traceStep`, `iterateLearner-clock`.
- Produces: explicit recurrence and arbitrary-depth statements.

- [ ] Add an explicit `trace-depth-recurrence` theorem.
- [ ] Preserve `traceGRU-unbounded` for every finite `n : Nat`.
- [ ] Add a theorem exposing unbounded time-step count through the learner clock.
- [ ] Document the finite-carrier caveat: arbitrary finite depth is proved, but infinite state/function cardinality is not claimed for `Int8`.

### Task 4: Remove regret from the active benchmark surface

**Files:**
- Modify: `Exotic/ERL/FullCoupled/GeneralClosedLoopBenchV2.agda`
- Modify: `.ci/discovery/ExplorationTheoremGenerator.hs`
- Modify: `docs/GENERAL_CLOSED_LOOP_BENCH_LATEST.md`

**Interfaces:**
- Consumes: current return/success/steps/distinct-actions benchmark semantics.
- Produces: benchmark records and discovery checks without a truncated-subtraction pseudo-regret field.

- [ ] Remove `regret` from `LoopResult`.
- [ ] Update all constructor calls and active metric checks.
- [ ] Remove active `check-*-regret` discovery symbols.
- [ ] Remove regret claims from the latest active benchmark document.

### Task 5: Validate repository state

**Files:**
- Read: `.github/workflows/agda.yml`
- Read: current GitHub tree and changed files.

**Interfaces:**
- Consumes: all previous tasks.
- Produces: verified commit lineage and a precise statement of what was and was not CI-checked.

- [ ] Confirm theorem closure file is gone and monolith is present.
- [ ] Confirm active benchmark no longer exposes regret.
- [ ] Confirm latest commit SHA.
- [ ] Do not report CI as green unless a fresh run is observable.
