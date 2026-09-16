# Unconditional Canonical Learner Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement the plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace assumption-bearing canonical convergence/cycle claims with source-local contradiction and deduction theorems derived directly from the clocked learner transition, while retaining the complete environment-agnostic Watkins/LCB/sparsemax/q-log/attention/Walsh/GRU/F4 learner composition.

**Architecture:** The canonical Agda file owns every active learner definition and imports no project-local module. Unconditional theorem strength comes from definitional equalities plus Nat monotonicity of `clock` and `totalCount`; no Lyapunov witness, environment law, probability assumption, or postulate is added.

**Tech Stack:** Agda 2.8.0, stdlib 2.4, `--safe`; Haskell generator and redundancy audit.

**Spec:** `docs/THEOREM_FIRST_REPLICATION_WIKI.md`

## Global Constraints

- Canonical learner file has zero project-local Agda imports.
- No environment, replay, probability, posterior, or statistical carrier occurs in canonical state.
- Watkins is the sole learned Q/action-selection source.
- Learned sparsemax attention remains learner representation state and feeds the recurrent path.
- No holes, postulates, or wildcard proof terms in maintained Agda sources.
- No canonical theorem may gain strength by introducing a certificate record as an extra premise.
- Safe Agda remains the acceptance oracle.

---

### Task 1: Make the canonical transition fully endogenous

**Files:** `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

- [x] Keep Watkins, LCB, fixed-temperature sparsemax, negative q-log shaping, learned attention, Walsh, hard-sign Mobius GRU, F4/L2, NormPair, and the complete state in one file.
- [x] Route `canonicalSignal` through the current endogenous q-log control.
- [x] Route the actual learned attention representation through Walsh into `canonicalGRUStep`.
- [x] Keep environment/statistical types absent from the file.

### Task 2: Replace assumption-bearing cycle claims

**Files:** `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

- [x] Prove `canonicalStep-not-fixed` by contradiction from `clock := suc clock`.
- [x] Prove `clockAfter` by induction.
- [x] Prove `canonicalAperiodic` from `clockAfter` and Nat non-self-return.
- [x] Prove `canonicalOrbitNonFixed` by deduction from `canonicalStep-not-fixed`.
- [x] Prove `canonicalNoNontrivialFiniteCycle` by contradiction without a Lyapunov premise.
- [x] Prove `canonicalTotalCountStep` by constructor reduction.
- [x] Prove `canonicalNoCountedTwoCycle` by contradiction from `suc (suc n) != n`.

### Task 3: Regression and generated status

**Files:**
- `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda`
- `.ci/discovery/ExplorationTheoremGenerator.hs`
- `.ci/CheckForbiddenTheorems.hs`
- `.github/workflows/agda.yml`

- [x] Regression-import the canonical monolith and assert the fixed-temperature, q-log, Mobius, persistence, policy-separation, clock, count, aperiodicity, and cycle theorems.
- [x] Require all unconditional theorem symbols from the generator.
- [x] Reject holes and postulates before Agda type checking.
- [x] Run both canonical source and regression through `agda --safe` in the workflow definition.

### Task 4: Documentation

**Files:** `docs/THEOREM_FIRST_REPLICATION_WIKI.md`

- [x] Remove claims that require a `FullLearnerCoerciveQuadratic` assumption.
- [x] Record the clock contradiction and count contradiction as the canonical cycle proofs.
- [x] State explicitly that no statistical convergence theorem is implied.

### Task 5: Final acceptance

- [ ] Fresh GitHub Actions canonical learner gate passes. Current run: `35065377146` was started from the pre-ledger head; a fresh run for the latest head is expected from the push event.
- [ ] Generated theorem report is produced from the exact canonical source and passes `agda --safe`.
- [x] No hole/postulate scanner failure occurred before the Agda step on the prior exact head.
