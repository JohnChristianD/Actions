# Generalized Sparsemax KKT and Theorem Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the generalized theorem surface around the learner monolith, with exact finite KKT certificate machinery, explicit LCB-policy semantics, Mobius/GRU depth laws, and CNN trajectory laws while refusing false equivalence claims.

**Architecture:** Keep learner definitions in `GeneralFullCoupledLearnerMonolith.agda`. Keep theorem proofs in `GeneralFullCoupledTheoremsMonolith.agda`, with `GeneralFullCoupledTheoremClosure.agda` as a thin theorem-family interpolation layer. The actual sparsemax scan-to-KKT proof remains separate until the learner support predicate is corrected and its finite sorting invariants are established.

**Tech Stack:** Agda 2.8.0, stdlib 2.4, `--safe`, GitHub Actions authoritative safe gate.

**Spec:** `docs/GENERAL_CLOSED_LOOP_BENCH.md`

## Global Constraints

- No new external algebra library is required merely to state the finite KKT certificate.
- Do not conflate sparsemax+LCB policy with sparsemax attention.
- Do not assert Euclidean real-valued sparsemax equivalence from the Int8/Nat scan without a semantic bridge.
- Prefer the minimal order machinery unless standard sort correctness removes substantial proof tedium.
- Keep direct commits on `main`, no PR workflow.

---

### Task 1: Repair theorem closure syntax and exact policy bridges

**Files:**
- Modify: `Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremClosure.agda`

- [ ] Fix the remaining parenthesis/scope issues.
- [ ] Keep learner-step clock, action, Q-update, count-update, iterator, Mobius prefix, semidirect, trace, and CNN bridge theorems definitionally exact.
- [ ] Verify the file imports only the existing theorem and learner monoliths plus core equality/Nat/Fin modules.
- [ ] Commit the repaired closure file.

### Task 2: Make the KKT certificate boundary honest and reusable

**Files:**
- Modify: `Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremClosure.agda`
- Modify: `Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremsMonolith.agda`

- [ ] Tie the certificate weight family directly to `L.sparsemaxWeight`.
- [ ] Expose exact numerator summation over `Fin A`.
- [ ] State simplex normalization, denominator equality, support non-emptiness, stationarity, and complementarity as explicit certificate fields until the scan construction proves them.
- [ ] Keep the theorem name distinct from the sparsemax-attention surface.
- [ ] Do not add a postulate or unsafe axiom.
- [ ] Commit the theorem-boundary pass.

### Task 3: Repair finite sparsemax support selection before claiming scan-to-KKT

**Files:**
- Modify: `Exotic/ERL/FullCoupled/GeneralFullCoupledLearnerMonolith.agda`
- Modify: `Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremClosure.agda`

- [ ] Correct the support criterion direction to match the threshold condition for descending scores.
- [ ] Handle the full-support case separately from the `k < A` case, because there is no `(k+1)`th score at full support.
- [ ] Prove the finite-list invariants needed by the support scan.
- [ ] Prove positive numerator iff score is above the derived threshold.
- [ ] Prove nonnegative numerator for every action.
- [ ] Prove numerator sum equals the common denominator.
- [ ] Derive primal simplex, stationarity, and complementarity for the finite scaled representation.
- [ ] Explicitly document that this is a discrete scaled sparsemax certificate, not yet a theorem over real Euclidean projection semantics.
- [ ] Commit the scan-to-KKT closure.

### Task 4: Wire the complete theorem closure into safe CI

**Files:**
- Modify: `.github/workflows/agda.yml`

- [ ] Add `GeneralFullCoupledTheoremClosure.agda` to the `agda --safe` checks.
- [ ] Keep the existing theorem monolith and benchmark checks intact.
- [ ] Run the workflow or inspect the resulting GitHub Actions status for the new commit.
- [ ] Record only observed status, not assumed status.
- [ ] Commit CI wiring.

### Task 5: Final theorem interpolation audit

**Files:**
- Modify: `docs/GENERAL_CLOSED_LOOP_BENCH.md`
- Modify: `GeneralFullCoupledTheoremsMonolith.agda` or closure file as required

- [ ] Cross-check every theorem family already present in the theorem monolith.
- [ ] Add missing definitional interpolation lemmas where theorems are only implicit in the definitions.
- [ ] Keep CNN comparison abstract and conditional on a commuting representation witness.
- [ ] Keep Mobius/GRU semidirect composition exact at finite Nat depths.
- [ ] Do not manufacture a universal CNN equivalence theorem.
- [ ] Commit the final theorem-surface documentation update.
