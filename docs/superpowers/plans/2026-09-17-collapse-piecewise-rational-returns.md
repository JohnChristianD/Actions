# Theorem Collapse and Piecewise-Rational Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Collapse the maintained generalized theorem surface into one self-contained Agda monolith, add a genuinely inductive finite piecewise-rational closure proof, and finish the hybrid proof-search plus benchmark return/reference-return audit without reintroducing regret.

**Architecture:** Keep the generalized learner as a standalone single-file learner. Make `GeneralFullCoupledTheoremsMonolith.agda` the single maintained theorem source by moving the finite theorem modules' definitions into it and deleting the redundant theorem files. Define piecewise-rational expressions structurally, prove closure by induction over finite composition, and separately audit the Haskell search oracle and all active game benchmark return fields.

**Tech Stack:** Agda `--safe`, Agda standard library, Haskell/Cabal hybrid theorem search, GitHub Actions.

**Spec:** User request on 2026-09-17: collapse theorems; prove finite piecewise-rational closure; evaluate MR15-GA vs evosax; assess reservoir/associative theorem claims; audit endogenous unbounded-depth polynomial/rational theorem claims; assess statistics/stochasticity representability; restore returns plus reference returns, but not regret, across all unpruned games after the theorem/search work.

## Global Constraints

- Direct commits to `main`; no pull requests.
- Keep Agda files `{-# OPTIONS --safe #-}`.
- Do not claim universal approximation, memoroid membership, stochasticity, or reservoir-universality unless the source types prove the required semantic structure.
- Keep `referenceReturn` where benchmark environments already expose it; do not add regret fields.
- Do not restore evosax or RandomSearch.
- Do not add Python or bash harness source files.

---

### Task 1: Inventory and theorem-source collapse

**Files:**
- Modify: `Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremsMonolith.agda`
- Delete after migration: theorem-only files whose definitions are copied into the monolith, including CNN pyramid, observability, negative Munchausen, finite norm, finite parameter, finite semidirect, finite Sion, Int8 stability, Jensen min-max, and related theorem-only surfaces.
- Modify: `.github/workflows/agda.yml` if any deleted theorem filenames are compiled directly.

**Interfaces:**
- Consumes: the existing generalized learner import `GeneralFullCoupledLearnerMonolith as L` and existing canonical learner symbols only where a migrated theorem explicitly needs them.
- Produces: one maintained generalized theorem module containing every migrated theorem definition under one namespace.

- [ ] **Step 1: Enumerate direct workflow and source references.**
- [ ] **Step 2: Copy each theorem body into the monolith with imports reduced to the exact symbols required.**
- [ ] **Step 3: Remove duplicate theorem modules after all references are redirected.**
- [ ] **Step 4: Run repository search for deleted module names and verify only the monolith remains as the theorem source.**
- [ ] **Step 5: Commit the structural collapse.**

---

### Task 2: Finite piecewise-rational closure

**Files:**
- Modify: `Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremsMonolith.agda`

**Interfaces:**
- Consumes: existing `FiniteRational`, `mobiusRatio`, and finite `hardSign` machinery from the generalized learner.
- Produces: a structural syntax of finite piecewise-rational expressions and induction theorems proving closure under the supported constructors.

- [ ] **Step 1: Introduce a finite piecewise-rational syntax over `Int8` input/output with constructors for constants, identity, rational/Mobius ratio, hard-sign branches, and finite composition.**
- [ ] **Step 2: Define evaluation into the existing finite rational carrier.**
- [ ] **Step 3: Prove evaluation is closed by constructor induction.**
- [ ] **Step 4: Prove finite composition preserves the class.**
- [ ] **Step 5: State the theorem as finite closure, not universal approximation.**
- [ ] **Step 6: Commit the closure proof.**

---

### Task 3: Hybrid proof-search and MR15-GA audit

**Files:**
- Modify: `.ci/discovery/ProofSearch.hs` only if the source audit finds a real mismatch.
- Modify: `proof-search.cabal` or `.github/workflows/agda.yml` only if the build invocation requires repair.

**Interfaces:**
- Consumes: current MCTS-style grammar search, MR15-GA-style population mutation, A* fallback, and Agda `--safe` oracle.
- Produces: an auditable hybrid search path with no `evosax` or `RandomSearch` dependency.

- [ ] **Step 1: Search for `evosax` and `RandomSearch` references and confirm zero hits.**
- [ ] **Step 2: Inspect the MR15-GA subcomponent and distinguish its implemented mutation/population behavior from full evosax feature parity.**
- [ ] **Step 3: Run the Cabal proof search through CI or local equivalent and record the actual candidate count/back-end behavior.**
- [ ] **Step 4: Commit only factual corrections.**

---

### Task 4: Returns and reference returns across active games

**Files:**
- Modify: all active closed-loop benchmark modules that expose a per-run result or environment ledger and currently lack return/reference-return fields.
- Modify: `.github/workflows/agda.yml` only if compilation targets need updating.
- Modify: `docs/BenchmarkReferenceLedger.md` if the field contract changes materially.

**Interfaces:**
- Consumes: existing game-specific reward/return computations and `referenceReturn` convention.
- Produces: consistent `return` and `referenceReturn` reporting for every unpruned game, with no `regret` field.

- [ ] **Step 1: Inventory every active game benchmark under `Exotic/ERL/FullCoupled`.**
- [ ] **Step 2: Add return/reference-return fields only where absent, deriving them from existing reward and reference ledgers.**
- [ ] **Step 3: Search for any `regret` fields and keep them absent.**
- [ ] **Step 4: Commit the benchmark reporting normalization.**

---

### Task 5: Verification and status ledger

**Files:**
- Modify: `docs/GENERAL_MONOLITH_STATUS_20260917.md` with the post-change verification facts.

**Interfaces:**
- Consumes: GitHub Actions results from generalized learner/theorem/benchmark checks and hybrid search.
- Produces: a truthful status record distinguishing passed, in-progress, timed-out, and unverified checks.

- [ ] **Step 1: Run the generalized theorem monolith check.**
- [ ] **Step 2: Run the generalized closed-loop benchmark checks.**
- [ ] **Step 3: Run the hybrid proof-search gate.**
- [ ] **Step 4: Re-run repository searches for `evosax`, `RandomSearch`, `.py`, `.sh`, and stale theorem module names.**
- [ ] **Step 5: Commit the final status update.**
