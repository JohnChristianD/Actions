# Exploration Proof Repair Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Replace stale exploration proof surfaces with self-contained finite transition models whose claims are accepted only through `Agda --safe`, while separating whole-coupled Noisy Nets from the gating-layer counterfactual.

**Architecture:** Give MR15, OpenES, and NoisyNet explicit finite transition relations and concrete proof terms. The Haskell generator reports `Proven` only after `agda --safe` succeeds. A separate generic theorem formalizes when gate-layer reachability lifts through a projection/lift assumption without claiming full learner/EA irreducibility.

**Tech Stack:** Agda `--safe`, existing Agda standard library/built-ins, Haskell generator, GitHub Actions.

**Spec:** `docs/THEOREM_FIRST_REPLICATION_WIKI.md`

## Global Constraints
- Agda `--safe` is the sole mathematical authority.
- No empirical claim becomes a theorem without a concrete finite-state proof.
- NoisyNet remains whole-coupled learner+exploration.
- The gate-layer result is explicitly counterfactual/abstract.
- The forbidden theorem-family guard remains mandatory.

## Tasks

### 1. MR15 proof surface
Files: `Exotic/ERL/Exploration/MR15Reachability.agda`, `.github/workflows/agda.yml`.
Replace stale missing imports with a self-contained finite MR15 abstraction. Provide `mr15IrreducibilityProof : ∀ s t → Reach mr15Step s t` and `mr15SelfLoopProof : ∀ s → mr15Step s s`. Compile this module explicitly under `--safe`.

### 2. OpenES proof surface and generator truthfulness
Files: `Exotic/ERL/Exploration/OpenESDyadic.agda`, `.ci/discovery/ExplorationTheoremGenerator.hs`, `.github/workflows/agda.yml`.
Define an explicit finite OpenES relation with neutral mutation and prove `openESIrreducibilityProof` and `openESSelfLoopProof`. Make generator status depend on successful `agda --safe`, never symbol presence alone. Compile the module directly in CI.

### 3. Coupled NoisyNet repair
Files: `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda`, `.github/workflows/agda.yml`.
Remove the fixed-parameter invariant from any relation claiming global irreducibility. Define mutable finite coupled gate/learner state with fresh finite-noise transition witnesses, then prove `noisyNetIrreducibilityProof` and `noisyNetSelfLoopProof`. Preserve the exact GateNN diagonal identity separately.

### 4. Gating-layer counterfactual theorem
Create `Exotic/ERL/Exploration/GatingLayerCounterfactual.agda`. Define explicit full→gate projection and gate→full lift assumptions; prove by induction that gate reachability lifts to the image under those assumptions. Do not claim that canonical ERL exploration is only on the gating layer. Compile under `--safe` and ledger the distinction.

### 5. Generated theorem status
Update `.ci/discovery/ExplorationTheoremGenerator.hs`, `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`, docs, and CI so statuses are deterministic and `Proven` means successful kernel checking.

### 6. Final verification
Run the workflow, inspect Agda logs, require repaired exploration modules and the forbidden-family guard to pass, then only report theorem status as kernel-checked.
