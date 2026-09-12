# Finite Exploration and Markov Kernel Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement one real finite non-Gaussian exploration kernel and prove only the recurrence/aperiodicity/ergodicity properties that follow from its actual transition relation.

**Architecture:** Represent the selected exploration mechanism as a finite transition function/probability table over a finite parameter state and explicit random symbol alphabet. Compare Noisy-Net-style parameter perturbation, finite MR15-style population transition, and finite OpenES-style population transition by proof cost and executable simplicity, then select exactly one without mixing mechanisms.

**Tech Stack:** Agda 2.8.0, standard library 2.4, finite `Fin`, `Vec`, `Nat`, equality, decidable comparisons where already available.

**Spec:** `docs/superpowers/specs/2026-09-12-endogenous-int8-learner-design.md`

## Global Constraints

- No continuous Gaussian theorem is imported as if it were an Agda theorem.
- The non-Gaussian exploration distribution is finite and explicitly represented.
- All transition probabilities used in retained theorems are exact finite values.
- Aperiodicity requires an actual self-loop proof.
- Irreducibility requires an actual finite reachability proof.
- Ergodicity/mixing claims are downstream corollaries only after those properties are proved.
- No population method may be combined with Noisy Nets inside one canonical transition kernel.

---

### Task 1: Finite non-Gaussian random alphabet

**Files:**
- Create: `Exotic/ERL/Exploration/FiniteNoise.agda`

**Interfaces:**
- Produces a finite random symbol type with an explicitly non-Gaussian probability mass function.
- Produces exact support, normalisation, and zero-mass/positive-mass lemmas.

- [ ] **Step 1: Write failing normalisation and support theorems.**
- [ ] **Step 2: Run `agda --safe` and confirm missing definitions.**
- [ ] **Step 3: Implement the finite distribution as a finite table over an exact arithmetic domain.**
- [ ] **Step 4: Prove total mass equals one and that the intended zero perturbation symbol has positive mass.**
- [ ] **Step 5: Commit.**

Commit message: `feat: add finite non-gaussian exploration law`

### Task 2: Noisy-Net-style parameter perturbation

**Files:**
- Create: `Exotic/ERL/Exploration/NoisyNetFinite.agda`
- Modify: `Exotic/ERL/Canonical/CanonicalOptimizer.agda`

**Interfaces:**
- Produces a finite perturbation of an Int8 parameter vector driven by `FiniteNoise`.
- Produces an explicit no-change event and support-reachability lemmas.

- [ ] **Step 1: Add failing self-loop and one-coordinate reachability statements.**
- [ ] **Step 2: Implement perturbation and prove the self-loop from the positive zero-noise symbol.**
- [ ] **Step 3: Prove the strongest finite reachability theorem actually supported by the perturbation alphabet; do not assert irreducibility over coordinates that the distribution cannot move.**
- [ ] **Step 4: Add the constructor as one selectable exploration mode without combining it with MR15/OpenES.**
- [ ] **Step 5: Run `agda --safe` and commit.**

Commit message: `feat: formalise finite noisy-net exploration`

### Task 3: Finite MR15-style population transition

**Files:**
- Create: `Exotic/ERL/Exploration/MR15Finite.agda`
- Modify: `Exotic/ERL/Canonical/CanonicalOptimizer.agda`

- [ ] **Step 1: Define a finite population size `2^p`, finite rank relation, dyadic success counter, and bounded step-scale state.**
- [ ] **Step 2: Define the MR15-style transition exactly, including success-rate threshold handling.**
- [ ] **Step 3: Prove finite-state closure and a self-loop condition where the finite rule permits one.**
- [ ] **Step 4: Prove or reject irreducibility by direct finite reachability.**
- [ ] **Step 5: Commit.**

Commit message: `feat: formalise finite mr15 population kernel`

### Task 4: Finite OpenES-style population transition

**Files:**
- Create: `Exotic/ERL/Exploration/OpenESFinite.agda`
- Modify: `Exotic/ERL/Canonical/CanonicalOptimizer.agda`

- [ ] **Step 1: Define a bounded finite perturbation alphabet, population, rank utility, and update rule.**
- [ ] **Step 2: Prove finite closure.**
- [ ] **Step 3: Prove or reject self-loop and reachability properties.**
- [ ] **Step 4: Commit.**

Commit message: `feat: formalise finite openes population kernel`

### Task 5: Compare mechanisms inside Agda

**Files:**
- Create: `Exotic/ERL/Exploration/ExplorationComparison.agda`
- Modify: `Exotic/ERL/Canonical/ConjectureDiscovery.agda`

- [ ] **Step 1: Encode a finite score record containing closure, self-loop, reachability, and executable-state-size predicates.**
- [ ] **Step 2: Populate it from the actual theorem proofs for each implemented mechanism.**
- [ ] **Step 3: Select exactly one canonical mechanism by a concrete finite proposition, not by `x ≡ x`.**
- [ ] **Step 4: Prune mechanisms whose proof obligations fail rather than creating fallback certificates.**
- [ ] **Step 5: Run aggregate `agda --safe` and commit.**

Commit message: `feat: choose exploration by kernel-checked obligations`

### Task 6: Aperiodicity and irreducibility

**Files:**
- Create: `Exotic/ERL/Exploration/FiniteMarkov.agda`
- Modify: `Exotic/ERL/Exploration/ExplorationComparison.agda`

- [ ] **Step 1: Define the finite state relation and one-step transition support for the selected mechanism.**
- [ ] **Step 2: Prove a self-loop at an explicitly named state using the finite random law.**
- [ ] **Step 3: Prove finite irreducibility by bounded path construction, or retain only the strongest communicating-class theorem if full irreducibility fails.**
- [ ] **Step 4: State finite recurrence/invariant-distribution results only from the proven finite transition relation.**
- [ ] **Step 5: Run `agda --safe` and commit.**

Commit message: `feat: prove finite exploration recurrence properties`

### Task 7: Mixing theorem surface

**Files:**
- Modify: `Exotic/ERL/Exploration/FiniteMarkov.agda`
- Modify: `Exotic/ERL/Canonical/ConjectureDiscovery.agda`

- [ ] **Step 1: Encode the finite-step convergence measure available in the chosen arithmetic domain.**
- [ ] **Step 2: Prove only a finite-horizon or combinatorial mixing bound that can be checked without importing real-analysis machinery.**
- [ ] **Step 3: Reject claims about spectral-gap arithmetic, logarithmic mixing-time formulas, or TV convergence unless the required finite algebra has actually been formalised.**
- [ ] **Step 4: Run aggregate `agda --safe` and commit.**

Commit message: `feat: add kernel-checked finite mixing results`
