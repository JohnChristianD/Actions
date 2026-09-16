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
- Generalized Walsh/hidden mixing width is constrained to `4^k`.
- Exact normalized Walsh orthonormality is not asserted inside `Z/256Z`; the exact maintained Int8 theorem is unnormalized `H4 H4^T = 4I`, with normalization requiring an explicit dyadic representation.

### Task 1: Endogenous complete learner

- [x] Keep Watkins, LCB, fixed-temperature sparsemax, negative q-log shaping, learned attention, Walsh, hard-sign Mobius GRU, F4/L2, NormPair, and complete state in one file.
- [x] Route `canonicalSignal` through endogenous q-log control.
- [x] Route learned attention through Walsh into `canonicalGRUStep`.
- [x] Keep environment/statistical types absent.
- [x] Keep GRU state-field names distinct from optimizer/L2 control accessors.

### Task 2: Contradiction, negation, and exact rank

- [x] `canonicalStep-not-fixed` from `clock := suc clock`.
- [x] `clockAfter` by induction.
- [x] `canonicalAperiodic` and orbit non-fixedness by deduction.
- [x] `canonicalNoNontrivialFiniteCycle` without an external Lyapunov premise.
- [x] `canonicalTotalCountStep` and `canonicalNoCountedTwoCycle`.
- [x] `canonicalFullStep-clock` corrected to `refl`.

### Task 3: GRU quotient and associative scan

- [x] Persistent quotient `GRUEquivalent`.
- [x] `gruStep-respects-equivalence`.
- [x] Endomorphism action composition and associativity.
- [x] Input scan and Mobius-labelled scan.
- [x] Pure-Int8 GRU/critic/Walsh counts and quotient counts.

### Task 4: Walsh width and exact H4 Int8 law

- [x] Add `PowerOfFour`.
- [x] Prove `canonicalWalshWidth-power4` for current width `4`.
- [x] Add explicit Int8 rows with `255` representing `-1 mod 256`.
- [x] Prove exact 16-entry Int8 Gram law through `H4GramLaw` and `walshHadamardOrthogonality4`.
- [x] Keep normalized orthonormality explicitly outside the modular inverse limitations.

### Task 5: Full-composition state accounting

- [x] F4 optimizer contributes five Int8 coordinates.
- [x] NormPair contributes two.
- [x] Watkins signal and attention coordinates included.
- [x] Walsh is transient in `FullLearnerState`, not stored.
- [x] Complete current stored Int8 projection is `23` coordinates.
- [x] Current full state is countably infinite because several `Nat` fields are unbounded.
- [x] Under scalar-persistent width generalization, Int8 storage is `d + 22`.

### Task 6: Hard sparsity

- [x] Exact hard-sparse witnesses.
- [x] Policy invariance under NormPair replacement.
- [x] Policy invariance under F4 state replacement carrying global L2.
- [x] Composition theorem `hardSparse-composition-normPair-F4-L2`.
- [x] Keep theorem explicitly local/structural, not a trajectory-wide sparsity-ratio or approximation theorem.

### Task 7: Minimum algebra and imports

- [x] Effective algebra identified as finite many-sorted data + Nat arithmetic + equality/negation + products + endomorphism monoid.
- [x] Ring/module/lattice/metric abstractions identified as unnecessary theorem premises.
- [x] Current direct imports audited: every imported symbol is used.
- [x] Current source requires stdlib as written.
- [x] Mathematical no-stdlib reconstruction recognized as possible only through a source-level replacement foundation.
- [ ] Replace stdlib imports only if an equivalent local foundation is actually compiled and passes the same safe regression surface.

### Task 8: Replication and pruning

- [x] Wiki is the replication authority.
- [x] Wiki corrected to exact H4 theorem, not a false full-orthogonality claim.
- [x] Wiki includes full state, quotient, and width bookkeeping.
- [x] Wiki records minimum effective algebra and current stdlib requirement.
- [x] Wiki records maximum unconditional hard-sparsity theorem.
- [x] Wiki records exact `V(s) = clock s`, unit increment, and `omega` ordering.
- [x] Current branch inventory contains no active `Noisy Nets`, `OpenES`, or `MR15` refs.
- [x] Redundancy audit remains dry-run by default and only zero-local-import candidates are eligible for deletion.

### Task 9: Regression, generation, and final acceptance

- [x] Regression test checks H4 law, power-of-four width, full 23-coordinate count, quotient, persistence, scan, hard sparsity, clock, and cycle exclusions.
- [x] Generator now requires the H4 theorem, width law, and full state count in addition to the existing closure.
- [x] Wiki synchronized with current source and CI fact.
- [x] Plan synchronized with current source and CI fact.
- [x] Forbidden-family/hole scan passed on commit `83a2...`; H4 parse failure was isolated.
- [ ] Fresh gate for current head `066ba7bb00525ee7539178c3e3c634e18b9744a3` must complete canonical Agda check.
- [ ] Same-head regression, theorem generation, redundancy audit, and generated report must complete before calling the branch green.

## Current acceptance fact

The prior `83a2...` gate passed the forbidden-family scan and Agda setup, then failed only because the initial nested 16-way H4 proof term had a parse error. The current source replaces that term with the local `H4GramLaw` record and the current test/generator surfaces require it. The fresh gate is `35079729383` and is currently in progress; its final result is the acceptance authority.
