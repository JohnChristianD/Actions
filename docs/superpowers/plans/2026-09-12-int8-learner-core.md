# Finite Int8 Learner Core Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement the actual finite learner/representation/TD core in Agda `--safe` using uniform Int8-compatible parameters and retain only kernel-proved algebraic theorems.

**Architecture:** Build small pure finite modules for activation, frozen Haar, finite vectors, attention/projection, critic/trace state, and the coupled update. The aggregate learner must compute a concrete next-state function; theorem modules prove properties of those functions rather than asserting certificates.

**Tech Stack:** Agda 2.8.0, standard library 2.4, existing `Exotic/efficient_chad`, `Exotic/ERL/Stages`, finite `Fin`/`Nat` arithmetic.

**Spec:** `docs/superpowers/specs/2026-09-12-endogenous-int8-learner-design.md`

## Global Constraints

- Agda `--safe` is the only mathematical authority.
- No postulates, holes, inert certificates, or proof-bypass machinery.
- Trainable scalar parameters use a uniform Int8 representation.
- Every retained theorem is attached to an implemented finite function.
- Preserve the existing external Tom Smeding proof unchanged.
- Do not introduce Python, mutable arrays, loops, or a second mathematical oracle.

---

### Task 1: Finite vector and Int8 parameter kernel

**Files:**
- Create: `Exotic/ERL/Finite/Int8Vector.agda`
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined.agda`

**Interfaces:**
- Produces `Int8Vector : Nat → Set`, finite vector constructors, coordinate access/update, exact addition, and a pointwise parameter state.
- Reuses `Exotic.efficient_chad.Int8.Int8` rather than redefining scalar Int8.

- [ ] **Step 1: Write the failing kernel checks**

Add aggregate uses for vector roundtrip, coordinate update, and pointwise addition before the definitions exist.

- [ ] **Step 2: Run `agda --safe` and record the expected missing-module or missing-name failure.**

Run: `agda --safe Exotic/ERL/FullCoupled/AllSafeCombined.agda`

Expected: failure naming the new unresolved vector interface.

- [ ] **Step 3: Implement the finite vector kernel.**

Use `Fin n → Int8` for the vector carrier, define a constructor from a finite coordinate function, pointwise scalar operations, and an exact extensional equality theorem by function congruence.

- [ ] **Step 4: Run the aggregate kernel check.**

Run: `agda --safe Exotic/ERL/FullCoupled/AllSafeCombined.agda`

Expected: the vector checks pass while later missing modules remain visible.

- [ ] **Step 5: Commit.**

Commit message: `feat: add finite Int8 vector kernel`

### Task 2: Activations and frozen Haar

**Files:**
- Create: `Exotic/ERL/Finite/Activation.agda`
- Create: `Exotic/ERL/Finite/Haar.agda`
- Test through: `Exotic/ERL/FullCoupled/AllSafeCombined.agda`

**Interfaces:**
- Produces finite `softsign`, `signReLU`, `cReLU` functions over the chosen finite scalar representation.
- Produces a frozen Haar transform for the selected finite width and a theorem exposing the exact transform law.

- [ ] **Step 1: Add failing theorem statements for activation totality and finite Haar action.**
- [ ] **Step 2: Run `agda --safe` and confirm the failures are due only to missing definitions.**
- [ ] **Step 3: Implement total finite activation functions.**
- [ ] **Step 4: Implement unnormalised finite Haar with exact integer arithmetic; do not claim dyadic orthonormality unless the normalisation is represented exactly.**
- [ ] **Step 5: Prove only the closure, involution/scaling, and finite-support facts that actually reduce or recursively close.**
- [ ] **Step 6: Run `agda --safe` and commit.**

Commit message: `feat: add safe finite activations and Haar`

### Task 3: Sparsemax/top-k algebra

**Files:**
- Create: `Exotic/ERL/Finite/Sparsemax.agda`
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined.agda`

**Interfaces:**
- Produces finite support selection, bounded-support top-k projection, and fixed-support projection/Jacobian laws where representable.

- [ ] **Step 1: Encode support masks and fixed-support projection before claiming global dyadic closure.**
- [ ] **Step 2: Add counterexamples for unsupported dyadic-closure cases, including support cardinality that introduces a non-dyadic divisor.**
- [ ] **Step 3: Run `agda --safe`; retain only statements that close.**
- [ ] **Step 4: Implement the strongest valid closure restriction, e.g. support cardinalities whose required division remains inside the chosen scalar domain.**
- [ ] **Step 5: Prove support bound, fixed-support idempotence, and any finite nonexpansiveness theorem that can be represented without unproved real analysis.**
- [ ] **Step 6: Run aggregate `agda --safe` and commit.**

Commit message: `feat: formalise finite top-k projection`

### Task 4: True Online TD finite state

**Files:**
- Create: `Exotic/ERL/Finite/TrueOnlineTD.agda`
- Modify: `Exotic/ERL/Stages/Stage03_LinearLearner.agda`
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined.agda`

**Interfaces:**
- Produces the finite trace state `(z, previousFeature, previousValue)` and a concrete True Online update over the finite vector domain.

- [ ] **Step 1: Write a failing theorem comparing the implemented one-step update with a separately defined finite forward-view target on a bounded horizon.**
- [ ] **Step 2: Run `agda --safe`; confirm the theorem is not accepted before implementation.**
- [ ] **Step 3: Implement the update with synchronous snapshots and exact finite arithmetic.**
- [ ] **Step 4: Prove the one-step finite-horizon equality when the hypotheses are satisfied.**
- [ ] **Step 5: Do not encode the unsupported claim that arbitrary infinite-horizon TD equals the one-step update for all alpha.**
- [ ] **Step 6: Run aggregate kernel checks and commit.**

Commit message: `feat: add finite true-online TD semantics`

### Task 5: Endogenous F4-Int update

**Files:**
- Create: `Exotic/ERL/Finite/F4IntLearner.agda`
- Modify: `Exotic/ERL/Stages/Stage06_CoupledLearner.agda`
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined.agda`

**Interfaces:**
- Produces a concrete per-feature learner state and one-step update combining parameter, residual, momentum, log-step, and trace components in a finite bounded representation.

- [ ] **Step 1: Add failing invariant statements for every stored residual identity.**
- [ ] **Step 2: Run `agda --safe` before implementation.**
- [ ] **Step 3: Implement the update with immutable state snapshots and exact arithmetic.**
- [ ] **Step 4: Prove each residual identity by direct reduction/congruence.**
- [ ] **Step 5: Add the finite one-step learner theorem that composes TD, activation, and parameter update.**
- [ ] **Step 6: Run aggregate kernel checks and commit.**

Commit message: `feat: implement finite F4 Int learner`

### Task 6: Remove obsolete theorem wrappers

**Files:**
- Modify: `Exotic/ERL/Stages/Stage01_FiniteAlgebra.agda`
- Modify: `Exotic/ERL/Canonical/ConjectureDiscovery.agda`
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined.agda`

- [ ] **Step 1: Remove theorem wrappers whose proof is only kernel reflexivity and which duplicate primitive reduction.**
- [ ] **Step 2: Replace configuration `x ≡ x` survivors with actual behavioural configuration predicates when such predicates are implemented.**
- [ ] **Step 3: Run `agda --safe` over the aggregate.**
- [ ] **Step 4: Commit the pruned proof surface.**

Commit message: `refactor: prune redundant safe theorem wrappers`

### Task 7: Real learner regression

**Files:**
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined_test.agda`

- [ ] **Step 1: Add concrete finite learner transition examples covering each activation and the chosen exploration-independent core.**
- [ ] **Step 2: Run `agda --safe` on both canonical source and regression.**
- [ ] **Step 3: Commit.**

Commit message: `test: gate concrete finite learner semantics`
