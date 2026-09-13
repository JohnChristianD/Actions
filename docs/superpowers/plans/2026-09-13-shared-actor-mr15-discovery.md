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

## Tasks

### 1. Exact semantic port of deleted Clojure local discovery

**Files:** `.ci/discovery/ClojureInvolutionCompat.hs`, `.github/workflows/safe-discovery.yml`

- [ ] Port `valid-index?`, `adjacent-swap`, `sign-flip`, `compose-local`, and `involution?` to pure Haskell over finite lists.
- [ ] Port `select-safe-rule` and `apply-safe-rule` with the same `add-suc-import` rule and idempotence behaviour.
- [ ] Run the compatibility program in CI.

### 2. Shared finite representation for actor and critic

**Files:** `Exotic/ERL/FullCoupled/SharedActorCritic.agda`, `Exotic/ERL/FullCoupled/AllSafeCombined.agda`

- [ ] Define one `sharedRepresentation` function.
- [ ] Define actor and critic heads that both consume it.
- [ ] Prove their representation inputs are definitionally the same function.
- [ ] Do not claim a DPG pullback theorem until a concrete finite pullback is implemented.

### 3. Current-MR15 reachability countertheorem

**File:** `Exotic/ERL/Exploration/MR15Reachability.agda`

- [ ] Define `Uniform` population states.
- [ ] Prove `emptyPopulation` is uniform.
- [ ] Prove current `mutate` preserves uniformity.
- [ ] Lift the invariant through `Reach`.
- [ ] Construct an explicit non-uniform spike population.
- [ ] Prove the current finite MR15 transition is not irreducible and therefore cannot satisfy its full aperiodicity obligation.

### 4. One-bit candidate obligation

**File:** `Exotic/ERL/Exploration/MR15OneBit.agda`

- [ ] Define a separate one-coordinate bit mutation with an explicit neutral/hold outcome.
- [ ] Prove the neutral self-loop.
- [ ] Keep connectivity as an independent obligation; do not infer it from the hold outcome.

### 5. CI and pruning

**Files:** `.github/workflows/agda.yml`, `.github/workflows/safe-discovery.yml`

- [ ] Compile shared actor/critic and MR15 proof surfaces with `agda --safe`.
- [ ] Compile the current theorem-obligation module without numeric scores.
- [ ] Run the exact Clojure semantic port through GHC/runghc.
- [ ] Remove the obsolete `TheoremRanking.agda` module.
