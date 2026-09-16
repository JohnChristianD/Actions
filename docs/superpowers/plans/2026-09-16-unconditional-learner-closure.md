# Unconditional Canonical Learner Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement the plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Maintain the canonical learner as a self-contained Agda `--safe` composition with unconditional contradiction/negation/deduction theorems, exact finite-carrier bookkeeping, a non-ring composition algebra, and a synchronized replication prompt.

**Architecture:** The canonical Agda file owns every active learner definition and imports no project-local module. Unconditional theorem strength comes from definitional equalities, persistent-state projection, endofunction composition, and Nat monotonicity of `clock` and `totalCount`. No environment law, probability assumption, Lyapunov premise, or postulate is added.

**Tech Stack:** Agda 2.8.0, stdlib 2.4, `--safe`; Haskell theorem generator and redundancy audit.

**Spec:** `docs/THEOREM_FIRST_REPLICATION_WIKI.md`

## Global Constraints

- Canonical learner file has zero project-local Agda imports.
- No environment, replay, probability, posterior, or statistical carrier occurs in canonical state.
- Watkins is the sole learned action-selection source.
- Learned sparsemax attention remains representation state and feeds the recurrent path.
- F4 optimizer, global L2 control, and NormPair remain explicit components of complete learner state.
- No holes, postulates, or wildcard proof terms in maintained Agda sources.
- No canonical theorem gains strength through an unstated certificate premise.
- `d` for a generalized Walsh/hidden mixing width is constrained to `4^k`; current scalar storage remains distinguished from a true vectorized implementation.
- Any exact normalized Walsh theorem must represent the dyadic normalization explicitly; powers of four alone do not create inverses of `2` inside `Z/256Z`.

### Task 1: Make the canonical transition fully endogenous

**Files:** `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

- [x] Keep Watkins, LCB, fixed-temperature sparsemax, negative q-log shaping, learned attention, Walsh, hard-sign Mobius GRU, F4/L2, NormPair, and the complete state in one file.
- [x] Route `canonicalSignal` through endogenous q-log control.
- [x] Route the learned attention representation through Walsh into `canonicalGRUStep`.
- [x] Keep environment/statistical types absent from the file.
- [x] Keep GRU state-field names distinct from the optimizer/L2 control accessor names.

### Task 2: Unconditional contradiction and rank theorems

**Files:** `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

- [x] Prove `canonicalStep-not-fixed` by contradiction from `clock := suc clock`.
- [x] Prove `clockAfter` by induction.
- [x] Prove `canonicalAperiodic` from `clockAfter` and Nat non-self-return.
- [x] Prove `canonicalOrbitNonFixed` by deduction from `canonicalStep-not-fixed`.
- [x] Prove `canonicalNoNontrivialFiniteCycle` by contradiction without an external Lyapunov premise.
- [x] Prove `canonicalTotalCountStep` by constructor reduction.
- [x] Prove `canonicalNoCountedTwoCycle` by contradiction from `suc (suc n) != n`.
- [ ] Fix the remaining `canonicalFullStep-clock` proof so it closes by definitional equality (`refl`) rather than applying `plus-zero` to a reflexive target.

### Task 3: GRU quotient, associative composition, and Mobius scan

**Files:** `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

- [x] Preserve `GRUEquivalent` as equality of the persistent matrices/noise/global-control projection.
- [x] Prove `gruStep-respects-equivalence` by persistence and transitivity.
- [x] Represent GRU transitions as endomorphisms with `GRUAction` and ordinary function composition.
- [x] Prove `gruActionAssociativity` and input-action associativity.
- [x] Add `gruMobiusAssociativeScan`.
- [x] Keep pure-Int8 counts for GRU, critic, Walsh, and GRU+critic+Walsh.
- [x] Keep the actual `HalfInt` path distinct from the explicit pure-Int8 counting carrier.
- [ ] Add a checked theorem/spec for the `d = 4^k` width constraint if and when the scalar hidden carrier is generalized to an explicit vector.

### Task 4: Full-composition state accounting

**Files:** canonical source and regression surface.

- [x] Account for F4 optimizer: five Int8 coordinates.
- [x] Account for NormPair: two Int8 coordinates.
- [x] Account for Watkins signal and attention coordinates.
- [x] Distinguish transient Walsh coordinates from stored full-state coordinates.
- [x] Record the actual current full-state Int8 count as `23` before the unbounded Nat fields and Boolean trace factor.
- [x] Record the width-`d` current-layout Int8 count as `d + 22`.
- [x] Record that `FullLearnerState` is countably infinite because of unbounded Nat fields.

### Task 5: Hard sparsity under NormPair + F4 + coupled L2

**Files:** `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

- [x] Preserve exact sparsemax witnesses for left/right hard sparsity.
- [x] Prove policy invariance under `NormPair` replacement.
- [x] Prove policy invariance under custom F4-state replacement carrying global L2.
- [x] Compose those equalities into `hardSparse-composition-normPair-F4-L2`.
- [x] Keep the result explicitly local/structural: no trajectory-wide sparsity theorem is inferred without an additional boundary-preservation premise.
- [ ] Do not add an unsupported universal approximation or analytic sparsity-ratio theorem.

### Task 6: Algebra/import minimization

**Files:** canonical source, test, and replication prompt.

- [x] Identify the effective algebra as finite many-sorted data plus Nat arithmetic, equality/negation, products, and the endomorphism monoid under composition.
- [x] Identify ring/module/lattice/metric abstractions as unnecessary theorem premises.
- [x] Audit the current imports as convenience-oriented and transitively broad rather than minimally exclusive.
- [x] Record that the current source needs stdlib as written, while a true no-stdlib implementation is logically possible with local replacements.
- [ ] Only replace stdlib imports after compiling an equivalent local foundation under the same `--safe` theorem surface.

### Task 7: Replication prompt and pruning synchronization

**Files:** `docs/THEOREM_FIRST_REPLICATION_WIKI.md`, `.ci/discovery/PruneRedundantLearnerModules.hs`, repository branch inventory.

- [x] Make the wiki the replication authority.
- [x] Correct the Walsh claim from full H4 orthogonality to the exact theorem actually present.
- [x] Add exact full-state and quotient accounting.
- [x] Add the `d = 4^k` constraint with the modular-normalization caveat.
- [x] Add the minimum effective algebra and stdlib assessment.
- [x] Record the hard-sparsity theorem at its maximum unconditional strength.
- [x] Record the exact Nat rank `V(s) = clock s` and unit increment.
- [x] The current remote branch inventory contains no active refs matching `Noisy Nets`, `OpenES`, or `MR15`.
- [x] Keep the redundancy audit as dry-run by default; only zero-import-user modules are eligible for deletion.

### Task 8: Regression, generation, and final acceptance

**Files:**
- `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda`
- `.ci/discovery/ExplorationTheoremGenerator.hs`
- `docs/THEOREM_FIRST_REPLICATION_WIKI.md`
- `docs/superpowers/plans/2026-09-16-unconditional-learner-closure.md`

- [x] Regression-test GRU quotient, input scan, Mobius scan, pure-Int8 counts, hard-sparsity composition, clock, counted progress, and cycle exclusions.
- [x] Generator requires the theorem symbols for the maintained closure surface.
- [x] Wiki and plan are synchronized to the live source and CI facts.
- [ ] Fix `canonicalFullStep-clock` in the canonical source.
- [ ] Re-run the canonical learner gate after the source fix.
- [ ] Require the same-head regression, theorem generation, redundancy audit, and generated-report checks to complete before calling the branch green.

## Current acceptance fact

The recorded gate for commit `d270eb0772b83215b1e54111eadcfc2ad334c1c7` installed Agda `2.8.0` and stdlib `2.4`, passed the forbidden-family/hole scan and tool setup, and then failed during canonical type-checking at `canonicalFullStep-clock` because `plus-zero (clock s)` was applied after the target was already definitionally reflexive. The direct source correction is the proof term `refl` for that theorem. A fresh gate is required after applying that source change.
