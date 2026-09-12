# Dyadic Safe Agda Prune Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the current Agda learner monolith and vendored Efficient-CHAD copy with a minimal `--safe` dyadic core, current official Agda setup with stdlib, and an external unchanged Tom Smeding dependency.

**Architecture:** `Exotic.ERL.Dyadic` becomes the canonical mathematical core. `AllSafeCombined` becomes a thin import surface instead of embedding learner/LSTM/QD machinery. CI installs Agda through `agda/agda-setup-action`, installs the matching standard library, clones Tom Smeding's repository without rewriting it, and checks both the local core and the unchanged upstream proof with `--safe`.

**Tech Stack:** Agda 2.8.0, Agda standard library 2.4, GitHub Actions, Tom Smeding `efficient-chad-agda`.

**Spec:** User request in chat dated 2026-09-12.

## Global Constraints

- Agda source must use `{-# OPTIONS --safe #-}`.
- No `postulate`, unsafe certificate, or floating-point primitive in the new canonical surface.
- Canonical learner state uses momentum-style sigma-delta state; other moment statistics are removed.
- Canonical arithmetic is integer/dyadic, with an unbounded dyadic representation plus a bounded lattice view.
- Exploration is confined to the representation/gating layer; OpenES, Noisy Nets, Gaussian/Tsallis probability machinery, MAP-Elites/CVT/archive theorems, and replay-oriented machinery are removed from the canonical surface.
- The local repository must not contain a rewritten or duplicated Tom Smeding Efficient-CHAD proof.

### Task 1: Replace monolith with dyadic core

**Files:**
- Create: `Exotic/ERL/Dyadic.agda`
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined.agda`

- [ ] Create a `Dyadic` record with integer numerator and natural exponent, exact addition, multiplication, negation, and power-of-two scaling.
- [ ] Keep the requested bounded `𝔻 n B` record as a lattice view over integer numerators.
- [ ] Define momentum state and a pure momentum update with one EMA state and residual carrier.
- [ ] Define bounded dead-zone and power-of-two step representation without transcendental operations.
- [ ] Remove the previous learner, LSTM, q-projection, exploration archive, and copied CHAD definitions from `AllSafeCombined.agda`.
- [ ] Make `AllSafeCombined` import only the new dyadic core and the external Tom wrapper surface.

### Task 2: Remove vendored/obsolete local Efficient-CHAD copies

**Files:**
- Delete: `Exotic/ERL/FullCoupled/EfficientCHADSourceToSource.agda`
- Delete: `Exotic/ERL/FullCoupled/EfficientCHAD_v164.agda`
- Delete: `Exotic/ERL/FullCoupled/EfficientCHAD_v164_test.agda`

- [ ] Delete each local copied proof after replacing all manifest references.
- [ ] Preserve Tom Smeding's upstream repository as an external CI dependency, without source rewriting.

### Task 3: Update canonical manifest and workflow

**Files:**
- Modify: `.ci/canonical-module.txt`
- Modify: `.github/workflows/agda.yml`
- Delete: `.ci/audit_tom_smeding.sh`
- Delete obsolete normalisation scripts that only repair the deleted monolith.

- [ ] Point the canonical manifest at `Exotic/ERL/FullCoupled/AllSafeCombined.agda` and a small safe regression module.
- [ ] Replace any legacy Agda setup with `agda/agda-setup-action@v1` and `agda-stdlib-version: '2.4'`.
- [ ] Add the upstream Efficient-CHAD checkout as an unmodified external include path.
- [ ] Run `agda --safe` on the local canonical module and upstream `chad-cost.agda` using the same toolchain.
- [ ] Fail explicitly if the unchanged upstream proof is not compatible with the current toolchain instead of rewriting it.

### Task 4: Verify and publish

**Files:**
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined_test.agda`

- [ ] Add exact equality checks for dyadic addition, multiplication, momentum reconstruction, and dead-zone identities.
- [ ] Commit the implementation on `refactor/dyadic-safe-prune`.
- [ ] Open a pull request against `main`.
- [ ] Inspect CI results and any review feedback before claiming completion.
