# GRU Coupled Safe Theorem Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the retired pointwise representation path with an Int8 GRU composition, keep the global optimizer and global L2 semantics, formalize flat dyadic exploration across Noisy Nets/OpenES/MR15 law permutations, and make the canonical Agda gate check only the resulting safe finite algebra.

**Architecture:** Use only existing Agda standard-library imports plus the repository's `Exotic.efficient_chad.Int8` module. Define finite gate surrogates, expose Mobius-style recurrence composition and scan laws, and lift each exploration method into the same finite law surface. Keep statistical claims out of the theorem surface.

**Tech Stack:** Agda 2.8.0, Agda standard library 2.4, existing Int8 CHAD module, existing GitHub Actions safe gate.

**Spec:** Current canonical replication prompt and GRU formulation in the conversation.

## Global Constraints

- Agda `--safe` is the mathematical authority.
- No analytic real-valued functions, irrational constants, non-dyadic probability values, or new imported Agda libraries.
- Global optimizer and global L2 remain part of every learned-component state.
- Pointwise forward activation paths, softsign-gated representation paths, CEM, and q_epsilon are retired from the canonical path.
- Flat dyadic is the canonical exploration probability-law module; OpenES, MR15-GA, and Noisy Nets remain method constructors over the same law interface.
- No environment-dependent statistical theorem is accepted.

---

### Task 1: GRU finite algebra

**Files:**
- Create: `Exotic/ERL/GRU/Int8GRU.agda`

**Interfaces:**
- `sigmoidDyadic8`, `signReLU8`, `gruCell`, `gruStep`.
- `Mobius`, `mobiusCompose`, `scanCompose`, `scan-assoc-law`.
- No imports beyond existing `Int8` and small standard-library primitives.

- [ ] Define finite gate surrogates and signReLU as Int8 operations.
- [ ] Define the recurrent cell with three recurrent matrix fields.
- [ ] Prove the finite forward identities used by the recurrence.
- [ ] Define sequential Mobius state transformers and associative composition.
- [ ] Prove the scan associativity law in the finite representation.

### Task 2: Coupled exploration law interface

**Files:**
- Create: `Exotic/ERL/Exploration/FlatDyadicLaw.agda`
- Create: `Exotic/ERL/Exploration/MethodLawCoupling.agda`

- [ ] Define flat dyadic weights over `Fin 256` with exact denominator and positive support witness.
- [ ] Parameterize MR15, OpenES, and GRU-NoisyNet method surfaces by the same law module.
- [ ] Prove the common neutral self-loop and finite reachability witnesses for the declared method abstraction.
- [ ] Derive period one only from irreducibility plus self-loop.

### Task 3: Canonical GRU composition and DPG closure

**Files:**
- Create: `Exotic/ERL/FullCoupled/GRUCoupled.agda`
- Create: `Exotic/ERL/FullCoupled/DPGInt8.agda`
- Modify: `Exotic/ERL/Stages/Stage05_Representation.agda`
- Modify: `Exotic/ERL/Stages/Stage06_CoupledLearner.agda`

- [ ] Define frozen Haar and dyadic RoPE as finite deterministic transforms.
- [ ] Define the GRU recurrent representation after the finite attention boundary.
- [ ] Carry global optimizer and global L2 fields through the coupled state.
- [ ] Define Int8 actor-critic equations with DPG-style transport and max-bootstrap target.
- [ ] Distinguish finite abstraction theorems from a future actual full-state transition theorem.

### Task 4: Canonical gate and pruning

**Files:**
- Modify: `.ci/canonical-module.txt`
- Modify: `.github/workflows/agda.yml`
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined.agda`
- Delete: superseded legacy normalization modules.

- [ ] Make GRU composition the canonical source/test pair.
- [ ] Add direct `agda --safe` checks for GRU, DPG, law/method modules, and generated theorem output.
- [ ] Remove canonical imports of econlib and old external Agda proof imports.
- [ ] Keep the Tom Smeding source as reference only; do not add its dependencies to the Agda import surface.

### Task 5: Generator closure

**Files:**
- Modify: `.ci/discovery/ExplorationTheoremGenerator.hs`
- Modify: `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`

- [ ] Generate law × method candidate permutations.
- [ ] Emit only finite dyadic candidate surfaces.
- [ ] Require checked survivors to pass `agda --safe`.
- [ ] Emit strict theorem-order witnesses only when a formal implication relation exists.

### Task 6: CI proof gate

- [ ] Run GitHub Actions on the branch.
- [ ] Inspect failures and repair actual safe-kernel failures.
- [ ] Require canonical source, canonical regression, GRU, DPG, law/method modules, generated candidates, and theorem-family checks to pass before PR completion.
