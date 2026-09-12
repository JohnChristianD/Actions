# Int8 Safe Agda Prune Implementation Plan

> **For agentic workers:** use the repository's Superpowers execution workflow. Keep each step kernel-checkable and delete superseded machinery.

**Goal:** replace the old Agda learner monolith and vendored Efficient-CHAD copy with a minimal `--safe` Int8-only surface, the official Agda toolchain, and an unchanged external Tom Smeding audit.

**Architecture:** `Exotic.efficient_chad.Int8` is the only active numeric representation layer. `AllSafeCombined` is a thin canonical composition root. Econlib GameTheory and Equilibrium counterparts consume the same Int8 representation. No separate dyadic module or file remains in the active Agda tree.

**Toolchain:** Agda 2.8.0, Agda standard library 2.4, GitHub Actions, Tom Smeding `efficient-chad-agda`.

**Global constraints**

- Every active Agda source uses `{-# OPTIONS --safe #-}`.
- No `postulate`, unsafe certificate, or floating-point primitive in the canonical surface.
- Int8 is the exclusive active numeric carrier: finite `Fin 256`, exact natural-indexed construction, and exact finite algebra.
- Do not add a parallel dyadic type, dyadic module, or dyadic-only helper file.
- GameTheory and Equilibrium certificates use Int8 payoffs/prices and exact finite equalities.
- Convergence statements remain finite stabilisation theorems, not informal real-analysis claims.
- The local repository contains no rewritten or duplicated Tom Smeding Efficient-CHAD proof.
- Retired QD/archive/CVT/OpenES probability machinery stays outside active semantics.

### Task 1: Int8 canonical surface

**Files**
- `Exotic/efficient_chad/Int8.agda`
- `Exotic/ERL/FullCoupled/AllSafeCombined.agda`
- `Exotic/ERL/FullCoupled/AllSafeCombined_test.agda`

- [x] Define `Int8` with `Fin 256`.
- [x] Define exact finite addition and multiplication through natural-indexed construction.
- [x] Keep CHAD primal/pullback structure on the Int8 carrier.
- [x] Keep the affine CHAD boundary on Int8.
- [x] Keep the active regression surface Int8-only.

### Task 2: Econlib counterparts

**Files**
- `Exotic/econlib/GameTheory.agda`
- `Exotic/econlib/Equilibrium.agda`

- [x] Define pure Nash certificates using Int8 payoff tables.
- [x] Prove the Prisoner's Dilemma defect-defect best-response certificate exactly.
- [x] Prove finite best-response stabilisation from every action pair.
- [x] Define finite Walrasian equilibrium and production-equilibrium certificates using Int8 prices/endowments/supply/demand.
- [x] Prove exact market-clearing stabilisation and a finite production-equilibrium existence witness.

### Task 3: Remove retired numeric and learner layers

**Files**
- Delete: standalone dyadic Agda implementation.
- Delete: superseded copied Efficient-CHAD and old monolith modules already outside the canonical root.
- Delete: stale CI repair scripts that target retired monolith formulations.

- [x] Remove active imports of the deleted dyadic layer.
- [x] Remove the retired dyadic workflow checks.
- [x] Keep Tom Smeding upstream as an external unchanged CI dependency.

### Task 4: CI and closure

**Files**
- `.ci/canonical-module.txt`
- `.github/workflows/agda.yml`
- `.github/workflows/representation-algebra-safe.yml`

- [x] Use `agda/agda-setup-action@v1`.
- [x] Pin Agda 2.8.0 and stdlib 2.4.
- [x] Check the Int8 module and canonical composition under `--safe`.
- [x] Keep the unchanged Tom Smeding probe explicit; incompatibility must fail rather than trigger source rewriting.
- [ ] Require fresh green kernel and canonical checks on the latest branch head.
- [ ] Enable squash merge only after all required checks are green.
