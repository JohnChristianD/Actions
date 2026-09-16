# Unconditional Canonical Learner Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement the plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Complete the canonical learner with source-local contradiction, negation, deduction, quotient, associative-scan, and hard-sparsity theorems while retaining the complete environment-agnostic Watkins/LCB/sparsemax/q-log/attention/Walsh/GRU/F4 learner composition.

**Architecture:** The canonical Agda file owns every active learner definition and imports no project-local module. Unconditional theorem strength comes from definitional equalities, persistent-state projection, endofunction composition, and Nat monotonicity of `clock` and `totalCount`; no Lyapunov witness, environment law, probability assumption, or postulate is added.

**Tech Stack:** Agda 2.8.0, stdlib 2.4, `--safe`; Haskell theorem generator and redundancy audit.

**Spec:** `docs/THEOREM_FIRST_REPLICATION_WIKI.md`

## Global Constraints

- Canonical learner file has zero project-local Agda imports.
- No environment, replay, probability, posterior, or statistical carrier occurs in canonical state.
- Watkins is the sole learned Q/action-selection source.
- Learned sparsemax attention remains learner representation state and feeds the recurrent path.
- No holes, postulates, or wildcard proof terms in maintained Agda sources.
- No canonical theorem may gain strength by introducing a certificate record as an extra premise.
- Safe Agda remains the acceptance oracle.

### Task 1: Make the canonical transition fully endogenous

**Files:** `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

- [x] Keep Watkins, LCB, fixed-temperature sparsemax, negative q-log shaping, learned attention, Walsh, hard-sign Mobius GRU, F4/L2, NormPair, and the complete state in one file.
- [x] Route `canonicalSignal` through the current endogenous q-log control.
- [x] Route the actual learned attention representation through Walsh into `canonicalGRUStep`.
- [x] Keep environment/statistical types absent from the file.
- [x] Remove the Agda 2.8 `globalControl` accessor collision by giving GRUState distinct state-field names.

### Task 2: Replace assumption-bearing cycle claims

**Files:** `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

- [x] Prove `canonicalStep-not-fixed` by contradiction from `clock := suc clock`.
- [x] Prove `clockAfter` by induction.
- [x] Prove `canonicalAperiodic` from `clockAfter` and Nat non-self-return.
- [x] Prove `canonicalOrbitNonFixed` by deduction from `canonicalStep-not-fixed`.
- [x] Prove `canonicalNoNontrivialFiniteCycle` by contradiction without a Lyapunov premise.
- [x] Prove `canonicalTotalCountStep` by constructor reduction.
- [x] Prove `canonicalNoCountedTwoCycle` by contradiction from `suc (suc n) != n`.

### Task 3: GRU quotient, associative composition, and Mobius scan

**Files:** `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

- [x] Preserve the `GRUEquivalent` relation as equality of persistent matrices/noise/global-control projection.
- [x] Prove `gruStep-respects-equivalence` by transitivity and persistence.
- [x] Represent GRU transitions as endomorphisms with `GRUAction` and ordinary function composition.
- [x] Prove `gruActionAssociativity` and input-action associativity for the scan law.
- [x] Add the explicit `gruMobiusAssociativeScan` alias theorem.
- [x] Add pure-Int8 coordinate counts for GRU, critic, Walsh, and the combined GRU+critic+Walsh carrier.
- [x] Keep the actual `HalfInt` Walsh path distinct from the explicit pure-Int8 counting carrier.

### Task 4: Hard sparsity under NormPair + F4 + coupled L2

**Files:** `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

- [x] Preserve exact sparsemax witnesses for left/right hard sparsity.
- [x] Prove policy invariance under `NormPair` replacement.
- [x] Prove policy invariance under the custom F4 state replacement carrying global L2.
- [x] Compose those equalities into `hardSparse-composition-normPair-F4-L2` without adding assumptions.

### Task 5: Regression, generation, and documentation synchronization

**Files:**
- `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda`
- `.ci/discovery/ExplorationTheoremGenerator.hs`
- `docs/THEOREM_FIRST_REPLICATION_WIKI.md`
- `docs/superpowers/plans/2026-09-16-unconditional-learner-closure.md`

- [x] Regression-test GRU quotient, input scan, Mobius scan, pure-Int8 counts, and hard-sparsity composition.
- [x] Require the new theorem symbols from the generator.
- [x] Synchronize the wiki with the exact finite state counts and with the non-ring/monoid distinction.
- [x] Correct the Walsh documentation so it does not claim full H4 orthogonality unsupported by the source.
- [x] Correct the hard-sparsity documentation to use the actual source witnesses.

### Task 6: Final acceptance

- [x] Prior gate failure diagnosed exactly: Agda 2.8 reported a `globalControl` clashing-definition in `GRUState` on head `6fab17a3ff7e64a941f39dd40e876ab9a47f6436`.
- [ ] Fresh latest-head canonical learner gate passes: run `35076378243` is currently the authoritative run for head `7a5ab2590582da6b6f38754d9331df84115eea8d`.
- [ ] Regression, theorem generation, redundancy audit, and generated report pass on that same head.
- [x] Hole/postulate/forbidden-theorem scan passed before the Agda step on the earlier exact head, and the current workflow continues to run it first.
