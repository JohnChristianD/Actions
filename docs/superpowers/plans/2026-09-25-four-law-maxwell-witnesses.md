# Four-Law Concrete Maxwell Semantic Witnesses Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add the smallest concrete Agda semantic layer that can inhabit the existing Law-I and Law-III witness contracts using classical electromagnetic/Hodge-Maxwell semantics, without weakening the contracts or asserting unconditional four-law closure.

**Architecture:** Keep the existing generic contracts unchanged. Add a specialized Maxwell semantic adapter module that supplies concrete physical state, trajectory/current compatibility, action/variation/stationarity data, and the learner-to-physical inverse only where the existing `CanonicalLearnerHodgeMaxwellCompositionTheorem` already supplies the required conditional bridge. Reuse the existing Hodge-Maxwell carrier rather than introducing a parallel physics representation.

**Tech Stack:** Agda `--safe`; existing `Exotic.ERL.FullCoupled` modules; existing Hodge-Maxwell representation; GitHub Actions/Nix verification.

**Spec:** `docs/research/nlab-four-law-semantic-candidates-2026-09-25.md` plus the typed contracts in `Exotic/ERL/FullCoupled/FourLawClosureWitnesses.agda`.

## Global Constraints

- Do not weaken `LawIPhysicsWitness`, `LawIIIVariationalWitness`, or `FourLawOneStepWitnessContract`.
- Do not introduce semantic axioms solely to populate missing fields.
- Do not use a trivial variation merely to satisfy Law III.
- Do not substitute the conservation slogan `dj = 0` for the exact repository obligation `current (trajectory p) ≡ current p`.
- Reuse existing Hodge-Maxwell representation data and the proved-conditional `canonical-physics-to-learner-transition-witness` where types actually align.
- External nLab material is semantic evidence, not Agda proof authority.
- Preserve `{-# OPTIONS --safe #-}`.
- Closure may be claimed only after an actual inhabited `FourLawOneStepWitnessContract` and the composed theorem are accepted by Agda and CI.

## Review Focus

1. **Current preservation:** the Law-I proof must establish the exact trajectory/current compatibility field, not merely differential-form current conservation.
2. **Nontrivial variation:** Law III must expose a genuine action/variation/stationarity structure; no vacuous inhabitant is acceptable.
3. **Representation alignment:** the specialized physical state must connect to the existing Hodge-Maxwell `Solution` carrier rather than silently defining a disconnected duplicate.
4. **Transition alignment:** the physics-to-learner step square must use the existing conditional adapter or a stronger explicitly proved specialization.
5. **Closure boundary:** if either semantic branch remains conditional, the graph and wiki must continue to say `FRONTIER`/missing rather than promoting a partial construction to closure.

---

### Task 1: Freeze the concrete Maxwell semantic boundary

**Files:**
- Create: `docs/research/four-law-maxwell-witness-design-2026-09-25.md`
- Modify: `docs/wiki.md`

**Interfaces:**
- Consumes: `LawIPhysicsWitness`, `LawIIIVariationalWitness`, `PhysicsToLearnerTransitionWitness`, `ContinuousHodgeMaxwellExactRepresentationData`.
- Produces: an explicit, reviewable choice of concrete carriers and equations before production Agda code.

- [ ] **Step 1: Record the carrier mapping.** State explicitly which existing Hodge-Maxwell `Solution` is the `PhysicalState`, what `Current` is, what `trajectory` means, and which equality will inhabit `trajectoryCurrentCompatibility`.
- [ ] **Step 2: Record the variational mapping.** State the action/Lagrangian carrier, variation carrier, admissibility predicate, and stationarity predicate. Require a nontrivial variation semantics.
- [ ] **Step 3: Record the learner bridge.** Identify the exact existing `encode`, `decode`, and step-conjugacy terms that can inhabit the transition witness, or mark the gap explicitly if their domains do not match.
- [ ] **Step 4: Update the wiki frontier description** with the selected concrete semantics and its remaining proof obligations.

**Expected result:** No production witness is added until the concrete types and proof obligations are explicit.

### Task 2: Add the Law-I Maxwell trajectory/current adapter

**Files:**
- Create: `Exotic/ERL/FullCoupled/FourLawMaxwellSemanticWitness.agda`
- Test/verify: the same module under the repository's safe Agda theorem gate.

**Interfaces:**
- Consumes: the concrete Hodge-Maxwell `Solution` carrier and differential-form/current fields already present in `TheoremsMonolith.agda`.
- Produces: a concrete `LawIPhysicsWitness` candidate with a proved `trajectoryCurrentCompatibility`.

- [ ] **Step 1: Add a failing proof obligation** in the new module whose target is the exact `trajectoryCurrentCompatibility` equality for the chosen current observable.
- [ ] **Step 2: Verify the obligation fails for the expected reason if the existing Hodge-Maxwell surface does not yet expose the needed trajectory theorem.
- [ ] **Step 3: Add only the minimal specialized trajectory/current definitions and theorem needed to prove the obligation.
- [ ] **Step 4: Re-run the focused Agda check and confirm the proof is accepted without unsafe flags or postulates.
- [ ] **Step 5: Expose the resulting Law-I witness constructor without changing the generic contract.

**Expected result:** Law I is either concretely inhabited or the precise missing mathematical theorem is recorded; no synthetic equality is introduced.

### Task 3: Add the Law-III Maxwell variational adapter

**Files:**
- Modify: `Exotic/ERL/FullCoupled/FourLawMaxwellSemanticWitness.agda`
- Create if needed: a narrowly scoped variational helper module under `Exotic/ERL/FullCoupled/`
- Document: `docs/research/four-law-maxwell-witness-design-2026-09-25.md`

**Interfaces:**
- Consumes: the same physical solution carrier selected in Task 1.
- Produces: a concrete `LawIIIVariationalWitness` with nontrivial variation, admissibility, action, and stationarity semantics.

- [ ] **Step 1: Write the smallest nontrivial variation theorem first, with an explicit stationary/critical-point predicate.
- [ ] **Step 2: Verify the theorem fails before the supporting definitions are introduced.
- [ ] **Step 3: Add the minimal action/Lagrangian and admissible-variation definitions required by the theorem.
- [ ] **Step 4: Prove stationarity/Euler-Lagrange semantics for the selected solution shell.
- [ ] **Step 5: Construct the Law-III witness and verify the focused Agda gate.

**Expected result:** Law III is inhabited only if the action/variation/stationarity semantics are genuinely proved.

### Task 4: Compose the one-step four-law contract

**Files:**
- Modify: `Exotic/ERL/FullCoupled/FourLawMaxwellSemanticWitness.agda`
- Modify: `Exotic/ERL/FullCoupled/TheoremsMonolith.agda` only if a new theorem consumer is necessary.
- Modify: `.ci/discovery/neural-function-class-separation-graph.json` only after the Agda inhabitant exists.

**Interfaces:**
- Consumes: Law-I witness, Law-III witness, existing conditional physics-to-learner adapter, and Law-IV statistical representation.
- Produces: an actual inhabitant of `FourLawOneStepWitnessContract`.

- [ ] **Step 1: Write the composition theorem against the existing contract.
- [ ] **Step 2: Verify it fails while either witness is absent.
- [ ] **Step 3: Compose the three proof-relevant seams without changing their definitions.
- [ ] **Step 4: Verify the one-step contract under `--safe`.
- [ ] **Step 5: Only then update the machine graph status from frontier/missing to the exact status justified by the inhabitant.

**Expected result:** A concrete one-step square exists, with no claim yet about prefix/horizon closure unless the next transport theorem is also instantiated.

### Task 5: Transport the inhabited square and update the knowledge layer

**Files:**
- Modify: `Exotic/ERL/FullCoupled/FourLawClosureWitnesses.agda` only if a concrete transport theorem needs a specialized wrapper.
- Modify: `.ci/discovery/neural-function-class-separation-graph.json`
- Modify: `docs/wiki.md`
- Modify: `docs/research/current-semantic-emergence-2026-09-25.mmd` if the graph projection changes.

**Interfaces:**
- Consumes: the inhabited one-step contract.
- Produces: justified n-step, prefix, and exact horizon closure edges using existing generic transport kernels.

- [ ] **Step 1: Instantiate `iterateConjugacy` with the concrete one-step witness.
- [ ] **Step 2: Instantiate `prefixScanConjugacy` with the input-indexed semantics where applicable.
- [ ] **Step 3: Connect the e-graph semantic transport only as a proof-preserving representation step.
- [ ] **Step 4: Update graph and wiki labels only for edges proved by Agda.
- [ ] **Step 5: Record any remaining frontier explicitly.

**Expected result:** The graph reflects proved composition, not aspirational closure.

## Final Verification

- [ ] Run the repository's scoped safe-Agda theorem/learner gates for touched modules.
- [ ] Run the Mercury theorem-only e-graph gate if graph/proof-discovery files changed.
- [ ] Run the repository's Dhall/CI validation required by the touched discovery and theorem surfaces.
- [ ] Inspect the final diff against this plan and the original nLab research note.
- [ ] Request an independent code review before merge.
- [ ] Record a tree-bound gate receipt with the exact proven tree and exit codes.
