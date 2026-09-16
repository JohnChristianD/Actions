# Redundant Component Pruning Audit Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the one-off q-log Python audit with one Haskell redundancy audit that covers the canonical learner's q-log, sparsemax action surface, learned-attention representation, Haar, GRU, LCB, optimizer, and retired duplicate component paths.

**Architecture:** The audit is read-only and reports duplicate or retired component implementations against explicit canonical owners. It does not delete mathematical sources automatically. The CI gate invokes it with the existing Haskell runtime, while Agda `--safe` remains the proof acceptance oracle.

**Tech Stack:** Haskell `runghc`, Agda 2.8.0, Agda stdlib 2.4, GitHub Actions.

**Spec:** The active implementation is `Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda`; learned sparsemax attention is representation state, not an independent actor, and the current GRU path consumes the canonical action-selection pair through Haar.

## Global Constraints

- The active finite learner remains deterministic and actor-free.
- Watkins is the only learned Q/action-selection source.
- Learned sparsemax attention remains a separate representation component.
- The current GRU theorem may only claim the actual canonical policy → Haar → GRU path.
- Haskell is automation only; Agda `--safe` is the acceptance oracle.
- New pruning automation is Haskell, Agda, or declarative environment configuration only, not a standalone Bash/Python script.
- Pruning is initially non-destructive and fails on stale retired sources or duplicate canonical-owned definitions.

---

### Task 1: Replace the obsolete q-log Python audit

**Files:**
- Delete: `.ci/prune-qlog-variants.py`
- Create: `.ci/discovery/PruneRedundantComponents.hs`
- Modify: `.github/workflows/agda.yml`

- [ ] **Step 1: Remove the obsolete Python audit.**

Delete `.ci/prune-qlog-variants.py`; the workflow must no longer invoke it.

- [ ] **Step 2: Add one Haskell audit covering all canonical-owned component families.**

The report must identify q-log, sparsemax action-selection, learned attention, Haar, GRU, LCB, optimizer, full-step, and retired-path duplication. A symbol is considered defined when its declaration line begins with the exact symbol name followed by `:` or `=` after whitespace normalization.

- [ ] **Step 3: Fail only on actionable duplication.**

The audit exits nonzero for an existing path on the retired-source list or an implementation of a canonical-owned unique symbol outside its declared owner. Shared component symbols that intentionally belong to their own canonical modules are allow-listed rather than misclassified.

- [ ] **Step 4: Wire the audit before Agda generation.**

Use `runghc .ci/discovery/PruneRedundantComponents.hs` and do not add a new shell script.

---

### Task 2: Add the composed persistent-GRU theorem

**Files:**
- Modify: `Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda`
- Modify: `Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2_test.agda`
- Modify: `.ci/discovery/ExplorationTheoremGenerator.hs`

- [ ] **Step 1: Add the exact canonical composition theorem.**

Prove:

```agda
canonicalPersistentGRUPreservation :
  ∀ {A : F4Scalar} (K : FullCoupledKernel A) (s : FullCoupledState A) →
    persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
canonicalPersistentGRUPreservation K s =
  persistent-preservation (gru s)
    (int8Add
      (canonicalSignal K s)
      (attentionToGRU K (haarApply (liftAttention (canonicalPolicy K s)))))
```

This is a genuine composed theorem: the actual no-actor Watkins/LCB action-selection signal, the finite Haar transform, the recurrent input projection, and the persistent GRU are all under the same canonical step.

- [ ] **Step 2: Add the theorem to the regression module.**

Expose the same proposition through a `check-canonical-persistent-gru` binding.

- [ ] **Step 3: Require the theorem in the Haskell theorem generator.**

Add `canonicalPersistentGRUPreservation` to the canonical theorem-family proof list.

---

### Task 3: Keep the theorem vocabulary honest

**Files:**
- Modify: `docs/THEOREM_FIRST_REPLICATION_WIKI.md`

- [ ] **Step 1: Clarify Haar versus associativity.**

State that Haar supplies the exact orthogonal-up-to-scale linear transform; associativity is a property of the separate Mobius composition operator, not of Haar multiplication.

- [ ] **Step 2: Record the new theorem.**

State that the composed canonical action-selection → Haar → GRU step preserves the persistent GRU coordinate exactly.

- [ ] **Step 3: Preserve the current architectural boundary.**

State that learned sparsemax attention remains a separate state representation and is not the source of the present GRU input.

---

### Task 4: Safe CI verification

**Files:**
- Review: `.github/workflows/agda.yml`
- Review: `Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda`
- Review: `Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2_test.agda`

- [ ] **Step 1: Run the redundancy audit.**

Expected result: no retired-path files and no duplicate canonical-owned definitions.

- [ ] **Step 2: Run `agda --safe` on the canonical V2 module and regression.**

Expected result: successful type checking, including `canonicalPersistentGRUPreservation`.

- [ ] **Step 3: Run the theorem generator.**

Expected result: `CanonicalLearner, status=Proven` only after the canonical V2 module typechecks.

- [ ] **Step 4: Treat any later CI failure as a real proof or dependency failure.**

Do not paper over Agda errors with generated-status text.
