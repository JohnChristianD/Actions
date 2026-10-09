# Learner Logical Specification and Graph-First CI Repair Plan

> **For agentic workers:** execute this plan blockers-first with one red-green verification slice at a time.

**Goal:** restore the canonical Agda/e-graph CI path, then make the learner's logical obligations discoverable as a machine-checked A*-style proof plan without claiming unproved Lyapunov descent.

**Architecture:** The existing canonical learner remains the executable semantic source. A separate Agda specification imports that source and names the optimizer transition, integer Lyapunov candidate, explicit descent obligation, and guarded-trace contract. The existing semantic search receives a separate learner obligation graph; its current inverse/search capabilities remain stable. Vehicle remains the network-boundary specification and is not treated as proof of the full state machine.

**Tech Stack:** Agda, TypeTopology, Agda2Hs, existing semantic/e-graph CI, Vehicle specification language.

**Spec:** User request on 2026-10-09: graph-first recursive CI repair; Vehicle-style learner specification; explain research/library composition.

## Global Constraints

- The existing canonical learner and theorem monolith remain the semantic source of truth.
- Do not state convergence unless strict descent / stability assumptions are proved or supplied explicitly.
- Do not treat `Int8` as bounded 8-bit arithmetic; the current carrier wraps unbounded `ℤ`.
- Keep the base inverse/exact-search A* plan and regression output stable.
- Preserve synchronized Mirth import/command markers.
- Verify through the pinned Nix/GitHub Actions CI; do not infer green from a successful Pages-only lane.

## Review Focus

- Equality products must be parenthesized so Agda parses intended product structure.
- Search nodes must not be mistaken for proof terms; the output is a plan of obligations.
- The Lyapunov descent premise must remain explicit until proven against the actual update.
- Vehicle's `@network` property must not be reported verified without a matching network/cache validation.
- The generated Agda-to-Haskell dependency graph must include the new logical-spec module.

---

### Task 1: Restore the graph's compile path

**Files:** `FullCoupled/CanonicalLearnerMonolith.agda`

- [x] Parenthesize the three-field parameter-persistence product.
- [ ] Re-run both the semantic/e-graph and learner/theorem CI lanes.
- [ ] Continue to the next concrete Agda error if either lane remains red.

### Task 2: Add an honest learner logical specification

**Files:** Create `FullCoupled/LearnerLogicalSpec.agda`; modify `FullCoupled/TheoremsMonolith.agda` only to import/expose it if required by source-closure generation.

- [ ] Define the integer-coordinate distance and nonnegative quadratic candidate on the existing optimizer state.
- [ ] Define the exact one-step descent proposition against `C.f4ThetaStep` / the canonical optimizer step.
- [ ] Define a certificate record whose fields state the proof obligations; do not postulate strict descent or claim it is established.
- [ ] Add a stable specification/step interface suitable for consuming from the theorem graph.

### Task 3: Extend A*-style graph search for learner obligations

**Files:** `FullCoupled/Agda2HsSemanticSearch.agda`

- [ ] Add separate learner capabilities/laws without changing existing generic inverse/search capabilities.
- [ ] Search the dependency chain from canonical step through the descent obligation and well-founded/guarded trace obligations.
- [ ] Add a kernel-checkable completeness regression and a compact report.
- [ ] Ensure the semantic source closure sees the new spec via a real Agda import edge.

### Task 4: Verify and review

- [ ] Run semantic-registry sync and source-closure checks.
- [ ] Run safe/kernel checking of both monoliths and the new spec.
- [ ] Run Agda2Hs extraction, GHC core lint, graph/e-graph regressions, and required-plan checks.
- [ ] Run full Nix connected-composition CI and confirm all required jobs are green on the same HEAD.
- [ ] Review claims around Vehicle, exact reals, CoRN/Rocq, and graph search for sound interface boundaries.
