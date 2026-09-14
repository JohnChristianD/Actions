# Lyapunov Composition Strengthening Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Strengthen the finite Int8 stability surface from constructive 2-cycle exclusion to exact exclusion of every nontrivial finite cycle and connect that result to the deterministic endogenous composition theorem surface.

**Architecture:** Keep the theorem constructive and hypothesis-driven. A Nat-valued strict Lyapunov certificate supplies the well-founded ranking; a finite cycle witness supplies the repeated state; strict descent around every cycle yields an impossible Nat inequality. The deterministic rollout/CHAD composition layer consumes the certificate without claiming stochastic ergodicity or automatic exploration.

**Tech Stack:** Agda 2.8.0, Agda standard library 2.4, `--safe`, finite Int8/dyadic carriers.

**Spec:** `docs/THEOREM_FIRST_REPLICATION_WIKI.md`

## Global Constraints

- No postulates, `unsafe`, `--without-K`, Float, Real, or non-dyadic numeric imports.
- Finite windows mean arbitrary finite lengths, not an infinite/unbounded cardinality theorem.
- Lyapunov exclusion requires an explicit strict-descent hypothesis.
- Deterministic GRU/DPG special cases must remain deterministic; stochastic Markov claims require explicit transition kernels/noise assumptions.

---

### Task 1: Repair canonical finite front-end elaboration

**Files:**
- Modify: `Exotic/ERL/FullCoupled/FiniteHaarSparsemaxRoPE.agda`

- [x] Add explicit `Int8Pair` binder annotations where Agda was leaving pair-component metas unresolved.
- [ ] Run canonical CI and verify the previous unresolved-meta failure is gone.

### Task 2: Prove general finite-cycle exclusion

**Files:**
- Modify: `Exotic/ERL/FullCoupled/Int8StabilityComposition.agda`

**Interfaces:**
- Produce an iterator over `Nat` steps.
- Produce a finite-cycle witness for `s`, cycle length `n`, and non-fixed cycle states.
- Prove strict Lyapunov descent along the cycle and contradiction by `<-trans`/`<-irrefl`.
- Retain the existing constructive 2-cycle theorem as the `n = 2` specialization boundary.

- [ ] Add the finite iterator definition.
- [ ] Add the cycle-state non-fixed predicate.
- [ ] Add the strict energy-descent induction over a positive cycle length.
- [ ] Add the all-n-cycle exclusion theorem.
- [ ] Add the theorem to the canonical workflow gate if it is not already transitively imported.

### Task 3: Compose stability with the endogenous deterministic boundary

**Files:**
- Modify: `Exotic/ERL/FullCoupled/EndogenousBoundaryComposition.agda`

- [ ] Add a stability certificate field to the full endogenous composition record.
- [ ] State deterministic special-case cycle exclusion as a composition theorem, without extending the result to stochastic-noise cases automatically.
- [ ] Keep DPG/max-Q equivalence conditional on the existing `IsGreedy` premise.

### Task 4: Update theorem-strength documentation

**Files:**
- Modify: `docs/THEOREM_FIRST_REPLICATION_WIKI.md`

- [ ] Record the strict ordering: fixed Sparsemax has the cleanest closed operator laws; F4-learned Sparsemax has a broader endogenous parameterized theorem class; Noisy learned Sparsemax adds a stochastic layer; CHAD adds a differentiable composition surface conditional on concrete primal/pullback certificates.
- [ ] Record that irreducibility, aperiodicity, invariant-measure existence, and ergodicity are not automatic from finite state or deterministic GRU alone.
- [ ] Record that Lyapunov strict descent excludes every nontrivial finite cycle, not merely 2-cycles.
- [ ] Record the Efficient-CHAD relationship as an imported mathematical design reference, while the canonical Agda proof remains the repository's explicit finite theorem layer.

### Task 5: CI verification and PR state

- [ ] Run the canonical Agda safe workflow and representation workflow on the repaired head.
- [ ] Inspect all failed logs and repair only evidenced compiler errors.
- [ ] Confirm green status checks.
- [ ] Merge PR32 only after the required checks are genuinely green and the GitHub merge operation is permitted.
