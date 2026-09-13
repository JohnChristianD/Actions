# Shared Actor, MR15 Reachability, and Exact Discovery Port Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Restore the finite shared-representation actor/critic boundary, formally expose the current MR15 reachability obstruction, and port the deleted Clojure local-discovery semantics without reintroducing Clojure as a mathematical authority.

**Architecture:** The learner monolith remains environment-agnostic and contains a single finite representation consumed by both actor and critic heads. Econlib remains outside that monolith. Exploration candidates are comparison modules with explicit obligations. The deleted Clojure machinery is reproduced behaviorally in pure Haskell orchestration and remains outside the Agda semantic authority; Agda `--safe` gates the mathematical claims.

**Tech Stack:** Agda 2.8.0 + stdlib 2.4, pure Haskell/Cabal tooling, GitHub Actions.

## Global Constraints

- Econlib GameTheory and Equilibrium remain separate environment modules.
- No numeric theorem ranking is canonical.
- No Gaussian/transcendental probability law is imported into the finite learner.
- Aperiodicity requires both a positive-support self-loop and the required communicating-class reachability theorem.
- Causal tape/replay equivalence is a pathwise semantics theorem, not an aperiodicity theorem.
- The current MR15 implementation must be disproved as irreducible over its full population space if its uniform-population invariant closes.
- A one-bit/one-coordinate mutation variant is a separate candidate theorem surface and must not be silently substituted for the current MR15 implementation.
- Actor and critic must consume the same finite representation function.

---

### Task 1: Exact semantic port of the deleted Clojure local-discovery machinery

**Files:**
- Create: `.ci/discovery/ClojureInvolutionCompat.hs`
- Modify: `.github/workflows/safe-discovery.yml`

- [ ] **Step 1:** Port `valid-index?`, `adjacent-swap`, `sign-flip`, `compose-local`, and `involution?` to pure Haskell over finite lists.
- [ ] **Step 2:** Port `select-safe-rule` and `apply-safe-rule` with the same rule identifier `add-suc-import` and idempotent rewrite semantics.
- [ ] **Step 3:** Add a `--check` mode reproducing the four deleted Clojure test properties.
- [ ] **Step 4:** Run the Haskell check in CI before safe Agda discovery.
- [ ] **Step 5:** Keep Agda `--safe` as the only mathematical gate.

### Task 2: Shared finite representation for actor and critic

**Files:**
- Create: `Exotic/ERL/FullCoupled/SharedActorCritic.agda`
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined.agda`
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined_test.agda`

- [ ] **Step 1:** Define a shared representation parameter record using the existing finite `Parameters` and `Window2`.
- [ ] **Step 2:** Define one `sharedRepresentation` function.
- [ ] **Step 3:** Define actor and critic heads that both consume `sharedRepresentation` and prove the dependency is the same function.
- [ ] **Step 4:** Keep updates finite and deterministic; do not claim a DPG gradient theorem until the pullback is explicitly defined.
- [ ] **Step 5:** Add regression witnesses that actor and critic use the same representation on the same window.
- [ ] **Step 6:** Compile the new module and aggregate with `agda --safe`.

### Task 3: True current-MR15 reachability countertheorem

**Files:**
- Create: `Exotic/ERL/Exploration/MR15Reachability.agda`
- Modify: `Exotic/ERL/Exploration/TheoremObligations.agda`
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined.agda`

- [ ] **Step 1:** Define `Uniform : Population -> Set`.
- [ ] **Step 2:** Prove `emptyPopulation` is uniform.
- [ ] **Step 3:** Prove every current `mutate` step preserves uniformity.
- [ ] **Step 4:** Lift that invariant through the finite `Reach` relation.
- [ ] **Step 5:** Construct an explicit non-uniform population and prove it is not uniform.
- [ ] **Step 6:** Conclude `¬ (∀ p q → Reach mr15Step p q)` for the current implementation.
- [ ] **Step 7:** Do not call this a statement about every MR15-GA implementation; it is a theorem about this finite mutation definition.

### Task 4: One-bit candidate obligation

**Files:**
- Create: `Exotic/ERL/Exploration/MR15OneBit.agda`
- Modify: `Exotic/ERL/Exploration/TheoremObligations.agda`

- [ ] **Step 1:** Define a separate one-coordinate bit-flip mutation with explicit `neutral` support.
- [ ] **Step 2:** Prove the neutral self-loop.
- [ ] **Step 3:** State the finite connectivity obligation for the bit-state graph.
- [ ] **Step 4:** Prove connectivity when feasible by bounded finite path construction; otherwise retain the obligation unproved rather than ranking it.
- [ ] **Step 5:** State aperiodicity only from the proved connectivity plus neutral self-loop.

### Task 5: Canonical separation

**Files:**
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined.agda`
- Modify: `.github/workflows/agda.yml`

- [ ] **Step 1:** Remove any remaining learner-gate import of Econlib modules.
- [ ] **Step 2:** Compile `GameTheory.agda` and `Equilibrium.agda` independently as environment targets.
- [ ] **Step 3:** Compile the learner aggregate without importing either environment module.
- [ ] **Step 4:** Compile the shared actor/critic and MR15 theorem modules as separate safe surfaces.

### Task 6: Replace fabricated ranking vocabulary

**Files:**
- Modify: `Exotic/ERL/Exploration/TheoremObligations.agda`
- Delete or compatibility-prune: `Exotic/ERL/Exploration/TheoremRanking.agda`

- [ ] **Step 1:** Ensure no numeric ranking exists.
- [ ] **Step 2:** Remove the word `Ranking` from canonical import and workflow surfaces.
- [ ] **Step 3:** Retain only theorem obligations and actual proofs/counterproofs.

---

Verification gate: run the exact Agda modules through `agda --safe`, run the Haskell compatibility check, then poll GitHub Actions for the current PR head. Do not call the work green until fresh CI confirms it.
