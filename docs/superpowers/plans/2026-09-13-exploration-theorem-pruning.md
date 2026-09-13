# Exploration Theorem Pruning Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove obsolete pure-DMCP artifacts and make the finite Agda theorem surface automatically generate and check irreducibility/aperiodicity obligations for MR15, OpenES, and Noisy Nets, including the coupled learner path.

**Architecture:** Keep Agda `--safe` as the sole acceptance oracle. Put reusable finite graph theorems in a small Agda schema, expose each exploration mechanism through a typed theorem interface, generate candidate checks from data-driven Haskell metadata, and make CI run the generated Agda checks. No statistical/data analysis is used.

**Tech Stack:** Agda `--safe`, existing `Exotic.efficient_chad.Int8`, small Haskell discovery generator, GitHub Actions.

**Spec:** Canonical Replication Prompt — theorem-first finite ERL/EA.

## Global Constraints

- Mathematical authority: Agda `--safe` only.
- Arithmetic: finite dyadic/int8 representation.
- No general measure-theory dependency is required for finite iid/expectation lemmas.
- Do not infer full-coupled irreducibility from exploration-only irreducibility.
- Keep Noisy Nets inside the coupled learner theorem surface.
- Delete pure DMCP distribution modules; do not reintroduce DMCP as a canonical distribution layer.
- Candidate generation may use Haskell, but Haskell never proves a theorem.

---

### Task 1: Remove obsolete pure DMCP artifact

**Files:**
- Delete: `Exotic/ERL/Exploration/DMCPDistribution.agda`
- Modify: `docs/REPLICATION_INDEX.md`
- Modify: `docs/THEOREM_FIRST_REPLICATION_WIKI.md`

- [ ] Delete the standalone DMCP distribution module.
- [ ] Remove DMCP-only references from live replication documentation.
- [ ] Do not reintroduce DMCP as a canonical exploration distribution module.

---

### Task 2: Add reusable finite exploration theorem schema

**Files:**
- Create: `Exotic/ERL/Exploration/ExplorationTheoremSchema.agda`

- [ ] Define finite reachability, irreducibility, and self-loop propositions.
- [ ] Define period-1 from full-state irreducibility plus an actual self-loop.
- [ ] Keep the schema independent of any single exploration distribution.

---

### Task 3: Put Noisy Nets inside the coupled learner theorem surface

**Files:**
- Create: `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda`
- Modify: `Exotic/ERL/Stages/Stage06_CoupledLearner.agda`

- [ ] Define finite Noisy-Net gate state with repository `Int8` arithmetic.
- [ ] Encode the noisy gate parameterization and exact diagonal identity.
- [ ] Expose the Noisy-Net transition as coupled learner state.
- [ ] State exact irreducibility/self-loop obligations for the actual coupled relation.
- [ ] Do not label full-coupled irreducibility proven until `agda --safe` checks the concrete proof.

---

### Task 4: Unify MR15, OpenES, and Noisy-Net theorem interfaces

**Files:**
- Modify: `Exotic/ERL/Exploration/MR15Reachability.agda`
- Modify: `Exotic/ERL/Exploration/OpenESDyadic.agda`
- Create: `Exotic/ERL/Exploration/ExplorationMethodChecks.agda`

- [ ] Expose support, reachability, and self-loop theorem obligations for each method.
- [ ] Preserve negative reachability results where a current relation is not irreducible.
- [ ] Distinguish proven irreducibility, proven non-irreducibility, and pending obligations.

---

### Task 5: Automate theorem candidate generation

**Files:**
- Create: `.ci/discovery/ExplorationTheoremGenerator.hs`
- Create: `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`
- Modify: `.github/workflows/agda.yml`

- [ ] Use data-driven metadata for MR15, OpenES, and Noisy Nets.
- [ ] Generate candidate Agda propositions for generator support, self-loop, irreducibility, aperiodicity, and coupled reachability.
- [ ] Emit only ordinary Agda source; no axioms or unsafe escape hatches.
- [ ] Run generated candidates with `agda --safe` in CI.
- [ ] Produce machine-readable theorem status without treating Haskell output as proof.

---

### Task 6: Update canonical theorem ledger

**Files:**
- Modify: `docs/THEOREM_FIRST_REPLICATION_WIKI.md`
- Modify: `docs/REPLICATION_INDEX.md`

- [ ] Record fresh independent dyadic mutation plus `D_tri` as the theorem-friendly canonical candidate.
- [ ] Keep entropy/variance/coverage comparisons criterion-parameterized.
- [ ] Record that Noisy Nets participates in the whole-coupled learner theorem surface.
- [ ] Remove live DMCP distribution-module references.

---

### Task 7: CI acceptance

**Files:**
- Verify: `.github/workflows/agda.yml`
- Verify: `.ci/canonical-module.txt`

- [ ] Generate candidate theorems.
- [ ] Check generated Agda under `--safe`.
- [ ] Check canonical Agda source and regression test.
- [ ] Verify deleted DMCP artifacts are not referenced by live canonical paths.
- [ ] Preserve explicit proven/disproven/pending theorem statuses.
