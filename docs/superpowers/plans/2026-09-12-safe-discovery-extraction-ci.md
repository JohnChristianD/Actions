# Safe Conjecture Discovery, Extraction, and CI Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn theorem discovery into a kernel-gated search loop and prove that Agda2HS extracts the actual finite learner into practical executable Haskell.

**Architecture:** Candidate theorem generation is pure syntax generation outside the mathematical authority. Each candidate is rendered into an Agda module, checked with `agda --safe`, and retained only when the kernel accepts it. The canonical module imports survivors transitively. Agda2HS is run against the actual learner module and compiled as an executable regression, while CI keeps the external proof immutable and prevents proof-bypass vocabulary.

**Tech Stack:** Agda 2.8.0, standard library 2.4, GHC 9.6/Cabal, Agda2HS, Bash, GitHub Actions.

**Spec:** `docs/superpowers/specs/2026-09-12-endogenous-int8-learner-design.md`

## Global Constraints

- Agda `--safe` remains the sole semantic authority.
- Haskell is search/orchestration/execution tooling only, not a mathematical oracle.
- No generated theorem may contain `postulate`, holes, unsafe primitives, or an inert reflexive certificate standing in for the requested property.
- Candidate failure is a normal pruning result, not a CI escape hatch.
- Agda2HS output must correspond to the actual learner source rather than a smoke placeholder.
- CI must fail closed when extraction or kernel checking fails.

---

### Task 1: Candidate syntax and bounded enumeration

**Files:**
- Create: `.ci/discovery/Candidate.agda`
- Create: `.ci/discovery/Enumerate.hs`

**Interfaces:**
- `Candidate.agda` defines the finite candidate theorem language and typed proof-shape vocabulary.
- `Enumerate.hs` emits finite batches of candidate modules by increasing syntax size and imports only ordinary text/process libraries.

- [ ] **Step 1: Add an Agda parser target with deliberately missing candidates so the gate fails.**
- [ ] **Step 2: Implement the finite candidate grammar and size measure in Haskell.**
- [ ] **Step 3: Emit candidates into `.ci/generated-conjectures/` with deterministic names.**
- [ ] **Step 4: Run `agda --safe` over one generated batch and prune failures.**
- [ ] **Step 5: Commit.**

Commit message: `feat: add typed safe conjecture enumeration`

### Task 2: Counterexample-guided pruning

**Files:**
- Modify: `.ci/discovery/Enumerate.hs`
- Create: `.ci/discovery/FiniteReject.agda`

- [ ] **Step 1: Encode finite counterexample environments for the supported algebraic domains.**
- [ ] **Step 2: Reject universally quantified candidate shapes when a finite counterexample is constructible before invoking expensive kernel checking.**
- [ ] **Step 3: Preserve the Agda kernel as the final acceptance gate even after counterexample filtering.**
- [ ] **Step 4: Commit.**

Commit message: `feat: add counterexample guided theorem pruning`

### Task 3: Survivor aggregation without inert certificates

**Files:**
- Modify: `Exotic/ERL/Canonical/ConjectureDiscovery.agda`
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined.agda`

- [ ] **Step 1: Replace constructor-only `x ≡ x` configuration survivors with concrete semantic propositions whose proof depends on implemented behaviour.**
- [ ] **Step 2: Import only survivor modules whose definitions are actually used by the learner.**
- [ ] **Step 3: Make the aggregate fail when a listed theorem disappears or stops type-checking.**
- [ ] **Step 4: Run `agda --safe` and commit.**

Commit message: `refactor: make conjecture survivors semantic`

### Task 4: Actual learner extraction

**Files:**
- Modify: `Exotic/efficient_chad/Agda2HSSmoke.agda`
- Create: `Exotic/ERL/Extraction/Agda2HSMain.agda`
- Modify: `.github/workflows/agda.yml`

- [ ] **Step 1: Replace the extraction target with the actual pure learner entry point while preserving the smoke fixture as a compatibility test.**
- [ ] **Step 2: Run Agda2HS locally in CI against the learner module.**
- [ ] **Step 3: Compile the generated Haskell with GHC 9.6 and run a finite learner transition example.**
- [ ] **Step 4: Fail if the generated module is empty, missing, or fails to compile.**
- [ ] **Step 5: Commit.**

Commit message: `feat: extract real learner with agda2hs`

### Task 5: Safe discovery workflow

**Files:**
- Modify: `.github/workflows/agda.yml`
- Create: `.ci/discovery/run-safe-discovery.sh`

- [ ] **Step 1: Run deterministic theorem enumeration in bounded batches.**
- [ ] **Step 2: Compile each candidate with `agda --safe`.**
- [ ] **Step 3: Record accepted candidates and remove failed candidates from the generated survivor set.**
- [ ] **Step 4: Run the canonical learner and regression modules after survivor aggregation.**
- [ ] **Step 5: Preserve failure logs as CI artifacts without treating logs as proofs.**
- [ ] **Step 6: Commit.**

Commit message: `ci: automate safe conjecture discovery`

### Task 6: Scheduled recurrence

**Files:**
- Modify: `.github/workflows/agda.yml`
- Create: `.github/workflows/safe-discovery.yml`

- [ ] **Step 1: Add a scheduled workflow that invokes the deterministic discovery script and the complete kernel/extraction gates.**
- [ ] **Step 2: Configure the schedule no more frequently than the supported repository limits and keep pull-request execution available.**
- [ ] **Step 3: Fail closed when the learner or proof surface regresses.**
- [ ] **Step 4: Commit.**

Commit message: `ci: schedule safe discovery loop`

### Task 7: Proof-surface audit

**Files:**
- Modify: `.ci/agda-repair.sh`
- Modify: `.github/workflows/agda.yml`
- Modify: `Exotic/ERL/Canonical/ConjectureDiscovery.agda`

- [ ] **Step 1: Add explicit checks rejecting `postulate`, holes, unsafe pragmas, and inert-certificate names in generated conjectures.**
- [ ] **Step 2: Keep allowlisted source normalisation deterministic and separate from theorem generation.**
- [ ] **Step 3: Run the complete `--safe` canonical/regression/extraction gate.**
- [ ] **Step 4: Commit the final proof-surface audit.**

Commit message: `ci: fail closed on proof bypasses`
