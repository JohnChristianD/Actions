# Exploration Theorem Pruning Implementation Plan

> **For agentic workers:** theorem generation is endogenous: actual explorer × retained dyadic law × softsign-gated representation boundary, with Agda `--safe` as the acceptance oracle.

**Goal:** Remove obsolete probability-law artifacts and make the finite Agda theorem surface generate endogenous irreducibility/period obligations for every actual explorer paired with the sole retained Flat Dyadic law after full coupling.

**Architecture:** Keep Agda `--safe` as the sole acceptance oracle. Put reusable finite graph theorems in a small Agda schema, expose MR15, OpenES, and Noisy Nets as actual exploration mechanisms, retain only Flat Dyadic as the active probability law, and compose the law with each method through a full algebraic coupling record anchored at the softsign-gated representation. Haskell only enumerates source combinations and invokes `agda --safe`.

**Tech Stack:** Agda `--safe`, existing `Exotic.efficient_chad.Int8`, small Haskell discovery generator, GitHub Actions.

**Spec:** Canonical Replication Prompt — theorem-first finite ERL/EA.

## Global Constraints

- Mathematical authority: Agda `--safe` only.
- Arithmetic: finite dyadic/int8 representation.
- No general measure-theory dependency is required for finite iid/expectation lemmas.
- Do not infer full-coupled irreducibility from exploration-only irreducibility.
- Keep Noisy Nets inside the coupled learner theorem surface.
- Retain only the checked Flat Dyadic probability law.
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
- Modify: `Exotic/ERL/FullCoupled/NoisyNetSoftsignFactor.agda`

- [x] Define finite Noisy-Net gate state with repository `Int8` arithmetic.
- [x] Encode the noisy gate parameterization and exact diagonal identity.
- [x] Expose the Noisy-Net transition as coupled learner state.
- [x] Prove the concrete projection/section/retraction and step projection/lift into `SoftsignGatedRepresentation`.
- [x] Exhibit a proper coupled-state fiber over the representation boundary.

---

### Task 4: Make the softsign-gated representation the canonical exploration boundary

**Files:**
- Modify: `Exotic/ERL/FullCoupled/SoftsignGatedRepresentation.agda`
- Modify: `Exotic/ERL/Exploration/MR15Reachability.agda`
- Modify: `Exotic/ERL/Exploration/OpenESDyadic.agda`
- Modify: `Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda`

- [x] Make MR15 state exactly `SoftsignGatedRepresentation = Int8 × Int8`.
- [x] Define OpenES as the scalar quotient/section of that representation.
- [x] Carry the canonical representation `PeriodOne` into `FullAlgebraicCoupling`.
- [x] Derive each method `PeriodOne` only inside the full coupling object.

---

### Task 5: Permanently retain only Flat Dyadic

**Files:**
- `Exotic/ERL/Exploration/FlatDyadic.agda`
- `Exotic/ERL/Exploration/DyadicLaw.agda`
- `.ci/check-forbidden-theorems.py`
- `.github/workflows/agda.yml`
- `docs/THEOREM_FIRST_REPLICATION_WIKI.md`
- `docs/REPLICATION_INDEX.md`

- [x] `DyadicLaw` contains only `flatDyadic`.
- [x] Remove obsolete non-flat law modules from the active source tree.
- [x] Remove obsolete law workflow checks.
- [x] Encode guard tokens for retired law identifiers so they cannot silently return.
- [x] Keep Flat Dyadic normalization, zero support, ±1 support, and universal support kernel-checked.

---

### Task 6: Automate the endogenous frontier

**Files:**
- Modify: `.ci/discovery/ExplorationTheoremGenerator.hs`
- Modify: `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`
- Modify: `.github/workflows/agda.yml`

- [x] Use metadata for MR15, OpenES, and Noisy Nets.
- [x] Use Flat Dyadic as the sole law metadata entry.
- [x] Generate exactly three composed theorem objects: one per actual method.
- [x] Require exact law normalization and unit-generator support in each object.
- [x] Require the canonical softsign-gated `PeriodOne` in each object.
- [x] Keep proof acceptance inside Agda.

---

### Task 7: Prove the strict method theorem order

**Files:**
- `Exotic/ERL/FullCoupled/TheoremStrengthV3.agda`
- `Exotic/ERL/FullCoupled/NoisyNetSoftsignFactor.agda`

- [x] Prove the OpenES quotient factor from MR15.
- [x] Prove the Noisy-Net factor from the coupled learner to MR15.
- [x] Transfer irreducibility, self-loop, and `PeriodOne` through both factors.
- [x] Exhibit explicit proper fibers for strictness.
- [x] Use the resulting semantic factor-extension chain `OpenES < MR15 < NoisyNet` as the structural theorem ordering.

---

### Task 8: Conditional Möbius composition

**Files:**
- `Exotic/efficient_chad/MobiusInt8Composition.agda`
- Create: `Exotic/efficient_chad/MobiusSoftsignBridge.agda`
- `Exotic/efficient_chad/SoftsignGatedComposition.agda`

- [x] Keep generic finite Möbius action composition kernel-checked.
- [x] Keep generic signReLU8→softsign8 CHAD forward/pullback composition kernel-checked.
- [x] Prove conditional composed Möbius closure from concrete activation witnesses.
- [x] Do not fabricate activation-specific signReLU8 or softsign8 Möbius witnesses.

---

### Task 9: CI acceptance

**Files:**
- Verify: `.github/workflows/agda.yml`
- Verify: `.ci/canonical-module.txt`

- [ ] Run a fresh current-head canonical gate.
- [ ] Check the strict factor theorem and conditional Möbius bridge under `--safe`.
- [ ] Check the generated three-way Flat Dyadic theorem harness under `--safe`.
- [ ] Preserve explicit proven/pending distinctions for any production semantics not connected to the finite kernels.
