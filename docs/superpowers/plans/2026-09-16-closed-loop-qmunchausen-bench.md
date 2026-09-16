# Closed-Loop q-Munchausen Benchmark Implementation Plan

> **For agentic workers:** Use superpowers:subagent-driven-development or executing-plans.

**Goal:** Replace the reward-only regression with a learner-policy-driven closed loop, formalize finite negative q-Munchausen as a sign-flipped endogenous analogue, record exact return/regret/success metrics, and keep the learner monolith environment-free.

**Architecture:** `CanonicalLearnerMonolith.agda` remains the single learner kernel. Games stay in modular port files. A new bridge maps the learner policy into each environment action, executes the environment, and feeds raw reward through standard or negative finite q-Munchausen before the next learner state.

**Tech Stack:** Agda 2.8.0, stdlib 2.4, `--safe`, exactly the eight direct stdlib modules already imported by the monolith.

## Global Constraints
- No holes, postulates, placeholders, or extra environmental/statistical assumptions.
- No new direct Agda imports.
- Default d = 64; power-of-four claims require explicit witnesses.
- Benchmark numbers are exact finite projections, not claims of bit-identical Gym/JAX execution.
- Standard vs negative q-Munchausen differs only by signed finite scale.
- Metrics are exact `Nat`: return, regret, success, steps.

## Tasks
- [x] Write failing closed-loop/q-Munchausen interface test.
- [ ] Implement `CanonicalQMunchausenClosedLoop.agda`.
- [ ] Replace the existing reward-only benchmark with one learner-policy-to-environment-action loop.
- [ ] Add standard vs negative q-Munchausen ceteris-paribus runs.
- [ ] Formalize current two-action sparsemax scope; do not import sorting libraries merely for convenience.
- [ ] Synchronize wiki and benchmark replication docs with exact theorem scope.
- [ ] Audit and prune stale v147/v149, EfficientCHAD, old closed-loop, and exploration artifacts only when unused.
- [ ] Update CI to compile only maintained theorem surfaces and the new regression.
- [ ] Run safe Agda, forbidden-surface, generator, and redundancy checks once at the final gate.
