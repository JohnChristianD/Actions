# Exact Int8 Transformer Learner and Agda Proof Pipeline Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the frozen finite learner with a genuinely learning, ordered Int8/dyadic Transformer actor-critic whose algebra, VJP, F4 update, irreducibility obligations, and Agda2HS executable all come from one canonical `--safe` Agda definition.

**Architecture:** Preserve the useful finite algebra and legacy monolith lessons, but delete duplicate/placeholder learner semantics. Build a focused canonical pipeline `E -> RoPE -> Pyr^top-k -> Fastfood -> sR1 -> sR2 -> GateNN -> Pi`, then compute a synchronous snapshot VJP and one parameter commit for `(xi, theta, psi, mu3, sigma3)` with three sigma-delta residual levels and an exponent floor. The proof layer establishes only theorems derivable from the actual finite transition; joint irreducibility is conditional on explicit reachability hypotheses rather than inferred from local noise support alone.

**Tech Stack:** Agda `--safe`, existing Int8/dyadic finite modules, Efficient-CHAD-style pure VJP, Agda2HS via Cabal, GitHub Actions.

**Spec:** `docs/superpowers/specs/2026-09-13-exact-int8-transformer-learner.md`

## Global Constraints

- Mathematical authority is `agda --safe` only.
- Arithmetic is finite Int8/dyadic; no transcendental or irrational constants.
- No Munchausen, Tsallis-2 distributional backup, softmax, replay, batching, or True Online TD in the canonical learner.
- Backup is standard TD(lambda) with hard max.
- Exploration is Noisy Nets at the gating layer only.
- Updates use synchronous snapshot semantics and one parameter commit.
- VJP is explicit/pure; no second autodiff authority.
- External repositories are implementation references only, never proof authorities.
- Agda2HS extracts the canonical learner, not a simplified surrogate.

---

- [ ] **Task 1: Lock the canonical specification and source surface**
  - Create `docs/superpowers/specs/2026-09-13-exact-int8-transformer-learner.md`.
  - Record the exact ordered composition, state record, update law, forbidden components, and theorem status policy.
  - Add a canonical-module manifest naming the new source and executable regression module.
  - Verification: specification contains no conflicting algorithm names and manifest paths exist.

- [ ] **Task 2: Replace placeholder CHAD surface with a typed finite VJP core**
  - Add a focused `Exotic/ERL/FullCoupled/FiniteVJP.agda` containing primal/pullback pairs and composition laws for the finite primitives actually used by the learner.
  - Reuse sound finite Int8 operations already present; do not reimplement arithmetic unnecessarily.
  - Prove primal preservation and chain-rule composition for the finite VJP operators that are used downstream.
  - Verification: `agda --safe Exotic/ERL/FullCoupled/FiniteVJP.agda`.

- [ ] **Task 3: Implement the canonical ordered Transformer representation**
  - Add `Exotic/ERL/FullCoupled/CanonicalTransformer.agda`.
  - Implement `E`, `RoPE`, top-k pyramid permutation, Fastfood permutation/sign stage, `sR1`, `sR2`, noisy gating, and final projection in the exact declared order.
  - State explicit permutation lemmas; never commute nonlinear operators without a proof.
  - Verification: exact order witness, stage-closure lemmas, and `agda --safe`.

- [ ] **Task 4: Implement actual learning state and synchronous one-commit transition**
  - Replace the frozen `FiniteLearner` semantics with a canonical learner state containing representation, critic, actor, gate parameters, residuals, traces, and dyadic step exponents.
  - Compute primal forward pass from a single state snapshot; compute all VJPs from that same snapshot; commit every learnable parameter exactly once.
  - Implement standard TD(lambda), hard max, actor update, and shared-representation update without replay/batching.
  - Verification: theorem that at least one learnable parameter changes on a concrete nonzero-gradient witness; theorem that the transition is single-commit and snapshot-based.

- [ ] **Task 5: Implement F4-Int and three sigma-delta levels with an exponent floor**
  - Add explicit quantised-coordinate/residual decomposition and `ell >= 0` floor.
  - Prove residual conservation and quantised-update correctness for finite dyadic increments.
  - Prove a local movement witness; do not claim irreducibility merely from residual accumulation.
  - Verification: finite update examples and `agda --safe`.

- [ ] **Task 6: Rebuild irreducibility/aperiodicity theorem layer from the real transition**
  - Add exact finite reachability relations for parameter, representation, gate, and joint states.
  - Prove the D_tri support-generation lemma separately.
  - Prove positive self-loop for the actual joint learner transition where the state/input witness makes it true.
  - State joint irreducibility as a theorem from explicit local movement/reachability hypotheses; if the current implementation cannot satisfy them, prove the counterexample instead of weakening the statement.
  - Derive finite-chain recurrence/unique-stationary consequences only after the preceding theorems are established.
  - Verification: `agda --safe` on the complete theorem module and constructive counterexample where an implication is invalid.

- [ ] **Task 7: Retire inconsistent canonical-path modules**
  - Remove the canonical workflow dependency on `TrueOnlineTD`, OpenES/MR15 exploration, replay, and frozen `ActualCoupledLearner` semantics.
  - Keep legacy modules only when they remain independently useful and non-authoritative.
  - Verification: repository search confirms banned algorithms are absent from the canonical learner surface.

- [ ] **Task 8: Make Agda2HS extract the actual canonical learner**
  - Update the Agda workflow to extract the new canonical module.
  - Add a small Haskell executable harness generated from that module and a deterministic finite witness/regression.
  - Ensure generated code is a translation of the same Agda definitions rather than a hand-written duplicate.
  - Verification: extraction succeeds and the executable witness agrees with the Agda witness values.

- [ ] **Task 9: Add one canonical CI gate**
  - Check the canonical source, regression proofs, Efficient-CHAD compatibility surface, extraction, and generated executable in one ordered workflow.
  - Keep external Efficient-CHAD checkout as provenance/tooling verification only.
  - Verification: fresh GitHub Actions run for the current PR head; report exact run IDs and failures rather than assuming success.

- [ ] **Task 10: Final proof audit and branch completion**
  - Run a line-by-line checklist against the specification.
  - Review that no theorem overclaims local noise support as full-chain irreducibility.
  - Verify PR status and current head after the final commit.
  - Only call the work complete when fresh CI evidence is available.
