# GRU Coupled Safe Theorem Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the retired pointwise representation path with an Int8 GRU composition, keep the global optimizer and global L2 semantics, formalize flat dyadic exploration across Noisy Nets/OpenES/MR15 law permutations, and make the canonical Agda gate check only the resulting safe finite algebra.

**Architecture:** Use only existing Agda standard-library imports plus the repository's `Exotic.efficient_chad.Int8` module. Define GRU gates with dyadic 0.5*(1+softsign) and signReLU over Int8, expose Mobius-style affine recurrence composition and scan laws, and lift each exploration law into the same coupled finite transition relation. Keep statistical claims out of the theorem surface.

**Tech Stack:** Agda 2.8.0, Agda standard library 2.4, existing Int8 CHAD module, existing GitHub Actions safe gate.

**Spec:** Current canonical replication prompt and GRU formulation in the conversation.

## Global Constraints

- Agda `--safe` is the mathematical authority.
- No transcendental functions, irrational constants, non-dyadic probability values, or new imported Agda libraries.
- Global optimizer and global L2 remain part of every learned-component state.
- Pointwise forward activation paths, softsign-gated representation paths, CEM, and q_epsilon are retired from the canonical path.
- Flat dyadic is the canonical exploration probability-law module; OpenES, MR15-GA, and Noisy Nets remain method constructors over the same law interface.
- No environment-dependent statistical theorem is accepted.

---

### Task 1: GRU finite algebra

**Files:**
- Create: `Exotic/ERL/GRU/Int8GRU.agda`
- Create: `Exotic/ERL/GRU/MobiusGRU.agda`

**Interfaces:**
- `sigmoidDyadic8`, `signReLU8`, `gruCell`, `gruStep`.
- `Affine2`, `mobius`, `mobius-compose`, `scan-compose`, `scan-assoc`.
- No imports beyond existing `Int8` and equality/natural/product primitives.

- [ ] Define the dyadic gate substitution and signReLU as finite Int8 operations.
- [ ] Define the recurrent cell using three recurrent matrices represented by finite matrix operations.
- [ ] Prove the pointwise forward identities by reflexivity or finite arithmetic lemmas.
- [ ] Define sequential Mobius state transformers and associative composition.
- [ ] Prove the scan associativity theorem in the finite representation.

### Task 2: Coupled exploration law interface

**Files:**
- Create: `Exotic/ERL/Exploration/FlatDyadicLaw.agda`
- Modify: `Exotic/ERL/Exploration/MR15Reachability.agda`
- Modify: `Exotic/ERL/Exploration/OpenESDyadic.agda`
- Modify: `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda`

- [ ] Define flat dyadic weights over `Fin 256` with exact normalization and positive support.
- [ ] Parameterize all three exploration methods by the law instead of embedding a named distribution.
- [ ] Prove the common zero-step self-loop and generator reachability properties for the law/method pair.
- [ ] Prove the method-independent coupled period-one consequence only after the actual coupled relation is supplied.

### Task 3: Canonical GRU composition and DPG closure

**Files:**
- Create: `Exotic/ERL/FullCoupled/GRUCoupled.agda`
- Create: `Exotic/ERL/FullCoupled/DPGInt8.agda`
- Modify: `Exotic/ERL/Stages/Stage05_Representation.agda`
- Modify: `Exotic/ERL/Stages/Stage06_CoupledLearner.agda`

- [ ] Define frozen Haar/log-pyramid preprocessing and dyadic RoPE as finite deterministic transforms, without treating either as a probability law.
- [ ] Define the GRU recurrent representation after sparsemax projection.
- [ ] Carry global optimizer and global L2 fields through the GRU state.
- [ ] Define Int8 actor-critic with DPG-style actor transport and max-bootstrap critic target as finite equations.
- [ ] Prove coupled neutral transition, reachability interface, and aperiodicity from the actual relation.

### Task 4: Canonical gate and pruning

**Files:**
- Modify: `.ci/canonical-module.txt`
- Modify: `.github/workflows/agda.yml`
- Modify: `Exotic/ERL/FullCoupled/AllSafeCombined.agda`
- Delete: canonical-only legacy files proven superseded by the GRU path.

- [ ] Make GRU composition the canonical source/test pair.
- [ ] Add direct `agda --safe` checks for GRU, DPG, all three method/law modules, and generated theorem output.
- [ ] Remove canonical imports of econlib and any transcendental/non-dyadic paths.
- [ ] Keep the Tom Smeding source as an audit reference only; do not add its dependencies to the Agda import surface.

### Task 5: Generator closure

**Files:**
- Modify: `.ci/discovery/ExplorationTheoremGenerator.hs`
- Modify: `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`

- [ ] Make candidate generation range over law × method × theorem-family permutations.
- [ ] Emit only finite dyadic propositions.
- [ ] Require every generated survivor to pass `agda --safe`.
- [ ] Emit strict theorem-order witnesses only when a formal implication relation is present; otherwise emit incomparable/unknown rather than inventing a ranking.

### Task 6: CI proof gate

- [ ] Run GitHub Actions on the branch.
- [ ] Inspect failed jobs and repair only actual safe-kernel failures.
- [ ] Require canonical source, canonical regression, GRU, DPG, all method modules, generated candidates, and forbidden-theorem checks to pass before PR completion.
