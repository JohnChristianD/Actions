# Exploration Theorem Pruning Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove obsolete pure-DMCP artifacts and make the finite Agda theorem surface generate endogenous irreducibility/period obligations for every actual explorer × dyadic law permutation after full coupling.

**Architecture:** Keep Agda `--safe` as the sole acceptance oracle. Put reusable finite graph theorems in a small Agda schema, expose MR15, OpenES, and Noisy Nets as actual exploration mechanisms, expose Lazy Walk and Dyadic Ladder as probability laws, and compose each law with each method through a full algebraic coupling record. Haskell only enumerates source combinations and invokes `agda --safe`.

**Tech Stack:** Agda `--safe`, existing `Exotic.efficient_chad.Int8`, small Haskell discovery generator, GitHub Actions.

**Spec:** Canonical Replication Prompt — theorem-first finite ERL/EA.

## Global Constraints

- Mathematical authority: Agda `--safe` only.
- Arithmetic: finite dyadic/int8 representation.
- No general measure-theory dependency is required for finite iid/expectation lemmas.
- Do not infer full-coupled irreducibility from exploration-only irreducibility.
- Keep Noisy Nets inside the coupled learner theorem surface.
- Keep Lazy Walk and Dyadic Ladder as probability-law modules, not standalone exploration mechanisms.
- The selectable law universe contains only the checked finite dyadic law modules.
- Candidate generation may use Haskell, but Haskell never proves a theorem.

---

### Task 1: Remove obsolete pure DMCP artifact

**Files:**
- Delete: `Exotic/ERL/Exploration/DMCPDistribution.agda`
- Modify: `docs/REPLICATION_INDEX.md`
- Modify: `docs/THEOREM_FIRST_REPLICATION_WIKI.md`

- [x] Delete the standalone DMCP distribution module.
- [x] Remove DMCP-only references from live replication documentation.
- [x] Do not reintroduce DMCP as a canonical distribution layer.

---

### Task 2: Add reusable finite exploration theorem schema

**Files:**
- Create: `Exotic/ERL/Exploration/ExplorationTheoremSchema.agda`

- [x] Define finite reachability, irreducibility, and self-loop propositions.
- [x] Define period-1 from full-state irreducibility plus an actual self-loop.
- [x] Keep the schema independent of any single probability law.

---

### Task 3: Put Noisy Nets inside the coupled learner theorem surface

**Files:**
- Create: `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda`

- [x] Define finite Noisy-Net gate state with repository `Int8` arithmetic.
- [x] Encode the noisy gate parameterization and exact diagonal identity.
- [x] Expose the Noisy-Net transition as coupled learner state.
- [x] State exact irreducibility/self-loop obligations for the explicit coupled relation.

---

### Task 4: Unify actual explorers and probability laws

**Files:**
- Create: `Exotic/ERL/Exploration/DyadicLaw.agda`
- Create: `Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda`
- Modify: `Exotic/ERL/Exploration/MR15Reachability.agda`
- Modify: `Exotic/ERL/Exploration/OpenESDyadic.agda`

- [x] Keep MR15, OpenES, and Noisy Nets as the actual explorer set.
- [x] Keep Lazy Walk and Dyadic Ladder as exact finite probability-law modules.
- [x] Carry exact law normalization and unit-support facts into the composition boundary.
- [x] Derive `PeriodOne` only inside `FullAlgebraicCoupling` from the composed irreducibility and self-loop proofs.
- [ ] Connect each law to the production mutation kernel semantics where the current explorer abstraction remains schematic.

---

### Task 5: Automate every law × method theorem permutation

**Files:**
- Modify: `.ci/discovery/ExplorationTheoremGenerator.hs`
- Modify: `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`
- Modify: `.github/workflows/agda.yml`

- [x] Use data-driven metadata for MR15, OpenES, and Noisy Nets.
- [x] Use data-driven metadata for Lazy Walk and Dyadic Ladder.
- [x] Generate exactly six composed theorem objects: three methods × two laws.
- [x] Emit only ordinary Agda source; no axioms or unsafe escape hatches.
- [x] Run generated candidates with `agda --safe` in CI.
- [x] Keep proof acceptance inside Agda.

---

### Task 6: Permanently prune the legacy triangular law

**Files:**
- Modify: `.ci/check-forbidden-theorems.py`
- Modify: `docs/THEOREM_FIRST_REPLICATION_WIKI.md`
- Modify: `docs/superpowers/plans/2026-09-13-exploration-theorem-pruning.md`

- [x] Remove the legacy triangular law from live theorem documentation.
- [x] Keep encoded guard tokens for its identifier spellings so the finite law universe cannot silently grow back.
- [x] Avoid broad substring tokens that create unrelated false positives.

---

### Task 7: CI acceptance

**Files:**
- Verify: `.github/workflows/agda.yml`
- Verify: `.ci/canonical-module.txt`

- [ ] Generate the six composed theorem artifacts.
- [ ] Check the dyadic-law interface under `--safe`.
- [ ] Check the full algebraic coupling module under `--safe`.
- [ ] Check the generated six-way theorem harness under `--safe`.
- [ ] Preserve explicit proven/pending theorem distinctions for any production-level semantics not yet connected to these finite abstractions.
