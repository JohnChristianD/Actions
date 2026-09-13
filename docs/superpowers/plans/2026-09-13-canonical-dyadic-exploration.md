# Canonical Dyadic Exploration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the repository's legacy finite noise and separate ES mutation laws with the single exact `D_tri` exploration law and kernel-check the finite mutation obligations.

**Architecture:** A focused `FiniteNoise` module owns the canonical 31-point support and exact weights. Noisy Nets, OpenES, and MR15-GA consume that common support rather than defining competing stochastic laws. Reachability is proved at the actual finite mutation relation; generation-chain irreducibility remains an explicit obligation until its full transition state is modeled.

**Tech Stack:** Agda 2.8.0, Agda standard library 2.4, `--safe`, existing Int8 finite modules, GitHub Actions.

**Spec:** `docs/superpowers/specs/2026-09-13-canonical-dyadic-exploration-design.md`

## Global Constraints

- Agda `--safe` is the mathematical authority.
- One stochastic exploration law: `D_tri(k) = (16 - |k|) / 256`, `k ∈ [-15,15]`.
- No floating-point, transcendental, or irrational constants.
- No literal non-dyadic `1/5`; MR15 adaptation uses integer comparisons.
- No claim of generation irreducibility without a complete finite transition relation.
- Fastfood/RoPE masks remain deterministic and are not additional sampling distributions.

---

### Task 1: Canonical D_tri support and exact weights

**Files:**
- Modify: `Exotic/ERL/Exploration/FiniteNoise.agda`
- Test: `Exotic/ERL/Exploration/FiniteNoise.agda`

**Interfaces:**
- Produces a finite noise type covering offsets `-15..15`.
- Produces exact natural-number weights summing to 256.
- Produces proofs of normalization, symmetry, zero mass, and Int8 support.

- [ ] **Step 1:** Define the finite support and weight function with the center weight 16 and mirrored weights 15..1.
- [ ] **Step 2:** Prove the total weight equals 256 by definitional reduction or finite arithmetic lemmas.
- [ ] **Step 3:** Prove the zero constructor has weight 16 and every support value lies in the Int8 range.
- [ ] **Step 4:** Prove symmetry of the signed offset and zero mean from pair cancellation.
- [ ] **Step 5:** Add exact variance `85/2` only if representable by the repository's existing finite rational layer; otherwise leave it as a separately named arithmetic theorem rather than inventing a new fraction encoding.
- [ ] **Step 6:** Check with `agda --safe`.
- [ ] **Step 7:** Commit the module-only change.

### Task 2: Migrate Noisy Nets and OpenES to D_tri

**Files:**
- Modify: `Exotic/ERL/Exploration/NoisyNetFinite.agda`
- Modify: `Exotic/ERL/Exploration/DyadicOpenES.agda`
- Modify: `Exotic/ERL/Exploration/TheoremObligations.agda`

**Interfaces:**
- Consumes the common `FiniteNoise` support.
- Produces shared perturbation/self-loop relations using the same support type.

- [ ] **Step 1:** Replace the three-point `Noise` pattern matching with canonical offset support.
- [ ] **Step 2:** Define scalar and vector perturbation through exact Int8 addition.
- [ ] **Step 3:** Preserve and prove the zero-noise self-loop using the canonical center constructor.
- [ ] **Step 4:** Update OpenES transition definitions to use the same support.
- [ ] **Step 5:** Remove the old three-point positive-mass assumptions.
- [ ] **Step 6:** Check all three modules with `agda --safe`.
- [ ] **Step 7:** Commit the migration.

### Task 3: Replace MR15 mutation with the canonical distribution

**Files:**
- Modify: `Exotic/ERL/Exploration/DyadicMR15GA.agda`
- Modify: `Exotic/ERL/Exploration/TheoremObligations.agda`

**Interfaces:**
- Produces an MR15 mutation step choosing one coordinate and one canonical `D_tri` offset.
- Keeps the existing exact integer step-adaptation rule.

- [ ] **Step 1:** Define the MR15 mutation event as `(coordinate, noiseOffset)` with `offset ∈ [-15,15]`.
- [ ] **Step 2:** Prove the zero-offset event is a self-loop at every population.
- [ ] **Step 3:** Prove `+1` and `-1` support witnesses.
- [ ] **Step 4:** Define a finite reachability relation over `Population = Fin dimension → Fin 256` using repeated single-coordinate unit moves.
- [ ] **Step 5:** Prove every population reaches every other population by coordinate-wise finite induction using the unit support witnesses and modular finite arithmetic.
- [ ] **Step 6:** Keep `oneFifthStepUpdate` as the exact integer comparison `5 * successes ≤ N`.
- [ ] **Step 7:** Replace the previous gate/exponent/sign obligation with the actual canonical distribution support obligation.
- [ ] **Step 8:** Check the MR15 and obligation modules with `agda --safe`.
- [ ] **Step 9:** Commit the mutation proof.

### Task 4: Correct the theorem boundary for generation chains

**Files:**
- Modify: `Exotic/ERL/Exploration/TheoremObligations.agda`
- Modify: `Exotic/ERL/FullCoupled/ActualCoupledLearner.agda` only if required to expose the exact finite state transition.

**Interfaces:**
- Produces separate mutation-level and generation-level obligations.
- Does not export an unsupported generation irreducibility theorem.

- [ ] **Step 1:** Keep `MutationSelfLoop` and `MutationReachability` as inhabited theorems.
- [ ] **Step 2:** Define the exact generation-state type only where the current implementation exposes all state components required by the transition.
- [ ] **Step 3:** State `GenerationIrreducibilityObligation` as an explicit proposition when the implementation does not yet provide a proof.
- [ ] **Step 4:** Ensure no theorem named as generation irreducibility is an alias of mutation reachability.
- [ ] **Step 5:** Check the affected modules with `agda --safe`.
- [ ] **Step 6:** Commit the theorem-boundary correction.

### Task 5: CI canonical gate and PR completion automation

**Files:**
- Modify: `.github/workflows/agda.yml`
- Modify: `.ci/canonical-module.txt` if needed to include the canonical exploration regression.

**Interfaces:**
- CI must check the canonical D_tri module, all migrated consumers, and the actual reachability theorem.
- PR automation may enable auto-merge only after GitHub reports the current head checks pass.

- [ ] **Step 1:** Add explicit `agda --safe` checks for every new canonical exploration module.
- [ ] **Step 2:** Remove checks tied only to obsolete three-point noise assumptions.
- [ ] **Step 3:** Preserve proof-bypass rejection and canonical learner checks.
- [ ] **Step 4:** Push sequential updates to the PR branch.
- [ ] **Step 5:** Poll workflow runs for the exact head SHA.
- [ ] **Step 6:** Only after a successful current-head kernel gate, approve the PR and enable auto-merge.

### Task 6: Final verification

**Files:**
- No source changes unless verification exposes a real defect.

- [ ] **Step 1:** Poll PR metadata and current head SHA.
- [ ] **Step 2:** Verify current-head workflow success, not merely an older commit's success.
- [ ] **Step 3:** Verify the canonical D_tri, mutation reachability, and self-loop modules individually with CI evidence.
- [ ] **Step 4:** Verify no competing exploration distribution remains in the canonical path.
- [ ] **Step 5:** Report only kernel-checked theorems as proved; keep residual obligations explicit.
