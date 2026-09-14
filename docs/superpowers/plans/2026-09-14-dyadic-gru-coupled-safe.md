# Dyadic GRU Coupled Safe Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace stale exploration abstractions with a finite dyadic full-coupling theorem surface for flat, lazy-walk, and dyadic-ladder laws across MR15-GA, OpenES, and recurrent Noisy Nets, while keeping Agda `--safe` authoritative.

**Architecture:** Use only finite Int8 algebra and existing Agda standard-library imports already present in the repository. Define exploration laws by finite support witnesses, compose each method with the same full finite recurrent representation state, and prove law/method closure, irreducibility, self-loop aperiodicity, and recurrent projection/lift. The recurrent representation is sparsemax projection, frozen Haar/Rademacher linear structure, dyadic RoPE encoding, and a GRU recurrence whose gate maps are finite softsign substitutions and whose candidate map is signReLU-style finite saturation; the theorem surface contains only finite dyadic operations.

**Tech Stack:** Agda 2.8.0 `--safe`, existing finite Int8 CHAD module, existing Agda standard library imports, existing GitHub Actions gate, Haskell discovery generator only as a candidate enumerator.

**Spec:** Current canonical replication prompt and the immediate dyadic GRU/full-coupling requirements in the task conversation.

## Global Constraints

- Agda `--safe` is the only mathematical acceptance oracle.
- Keep the global optimizer and global L2 semantics attached to every learned component.
- Do not add internal or external Agda libraries; reuse the existing finite Int8 module and existing imports.
- Keep the canonical theorem surface finite, dyadic, and algebraic.
- Do not claim environment-dependent statistical superiority.
- Flat dyadic, lazy unit walk, and dyadic ladder are probability-law modules for the existing methods, not new exploration methods.
- No pointwise MLP/forward activation outside the recurrent GRU representation.
- Keep Noisy Nets as a recurrent GRU perturbation method with perturbations on the three recurrent GRU matrices.

---

### Task 1: Establish finite dyadic law algebra

**Files:**
- Create: `Exotic/ERL/Exploration/DyadicLaws.agda`
- Replace: `Exotic/ERL/Exploration/FlatDyadicEligibility.agda`

**Interfaces:**
- Produces `FlatLaw`, `LazyLaw`, `LadderLaw` and finite support predicates.
- Produces `zeroSupport`, `unitSupport`, `generator`, and law eligibility records.

- [ ] Define all weights as natural dyadic numerators over denominator 256.
- [ ] Prove normalization by exact finite arithmetic.
- [ ] Prove each law has zero support, a unit generator, and symmetric support.
- [ ] Prove flat law has full finite support and therefore one-step reachability.
- [ ] Prove lazy and ladder laws generate all residues by repeated unit steps.
- [ ] Keep the theorem surface free of retired law families.

### Task 2: Define method/law full-coupled closure

**Files:**
- Create: `Exotic/ERL/FullCoupled/DyadicMethodLawCoupling.agda`
- Replace: `Exotic/ERL/Exploration/MR15Reachability.agda`
- Replace: `Exotic/ERL/Exploration/OpenESDyadic.agda`
- Replace: `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda`

**Interfaces:**
- Produces `Method`, `Law`, `CoupledState`, `CoupledStep`, `methodLawIrreducible`, `methodLawSelfLoop`, and `methodLawPeriodOne`.
- Produces a finite projection/lift simulation between method state and coupled representation state.

- [ ] Define the three methods as method tags, not separate probability laws.
- [ ] Couple every method to the same finite representation/learner/optimizer/L2 state.
- [ ] Prove law/method permutations preserve the same generator theorem when the law has unit support.
- [ ] Prove the full coupled self-loop from the zero-support witness.
- [ ] Prove irreducibility by unit-step paths for lazy and ladder laws and direct target for flat.
- [ ] Prove period one from full irreducibility plus the actual full-state self-loop.

### Task 3: Add recurrent GRU algebra and Mobius composition

**Files:**
- Create: `Exotic/ERL/FullCoupled/DyadicGRU.agda`
- Create: `Exotic/ERL/FullCoupled/MobiusGRU.agda`

**Interfaces:**
- Produces `GRUState`, three recurrent matrices, finite gate substitutions, `gruStep`, `mobiusCompose`, associative scan, and projection/lift theorems.

- [ ] Represent reset/update/candidate affine maps over existing Int8 operations.
- [ ] Use dyadic gate substitution `1/2 * (1 + softsign)` as a finite algebraic constructor.
- [ ] Use signReLU as a finite positive-branch constructor.
- [ ] Keep all three recurrent matrices under global optimizer and global L2 coupling.
- [ ] Prove Mobius composition identity and associativity at the finite operator level.
- [ ] Prove windowed associative scan and sequential equivalence.
- [ ] Prove Noisy Net recurrent projection/lift so recurrent exploration is connected to representation state rather than asserted from a standalone gate theorem.

### Task 4: Add sparsemax/Haar/RoPE finite representation theorem surface

**Files:**
- Create: `Exotic/ERL/FullCoupled/DyadicRepresentation.agda`

**Interfaces:**
- Produces `Sparsemax8`, frozen Haar transform, dyadic Walsh-Rademacher RoPE replacement, and representation composition.

- [ ] Model sparsemax as a finite projection relation with only finite arithmetic.
- [ ] Model frozen Haar as a finite deterministic linear transform.
- [ ] Model RoPE phase action with finite Walsh-Rademacher signs.
- [ ] Prove representation composition is finite and closed under Int8 operations.
- [ ] Prove recurrent projection/lift through this representation.

### Task 5: Complete DPG actor-critic finite theorem

**Files:**
- Create: `Exotic/ERL/FullCoupled/Int8DPG.agda`
- Replace: `Exotic/ERL/FullCoupled/SharedActorCritic.agda`

**Interfaces:**
- Produces finite actor, critic max-bootstrap, DPG transport, global optimizer/L2 coupling, and CHAD compatibility identities.

- [ ] Define deterministic Int8 actor and critic states.
- [ ] Keep critic max-bootstrap explicit as a finite argmax relation.
- [ ] Attach global optimizer and global L2 to both actor and critic updates.
- [ ] Prove actor update transport and critic bootstrap closure over the finite state.
- [ ] Prove coupling into the full representation/recurrent state.

### Task 6: Make discovery generator enumerate law/method permutations

**Files:**
- Replace: `.ci/discovery/ExplorationTheoremGenerator.hs`
- Replace: `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`

**Interfaces:**
- Generator emits every method × law candidate and records only Agda-safe survivors.

- [ ] Parameterize candidates by method and law tags.
- [ ] Require generated candidates to import the full coupled theorem module.
- [ ] Require every survivor to expose irreducibility, self-loop, period-one, projection/lift, and recurrent composition symbols.
- [ ] Keep Haskell as candidate generation only.

### Task 7: Make CI proof surface finite-only and green

**Files:**
- Replace: `.github/workflows/agda.yml`
- Replace: `.ci/canonical-module.txt`
- Replace: `Exotic/ERL/FullCoupled/AllSafeCombined.agda`
- Replace: `Exotic/ERL/FullCoupled/AllSafeCombined_test.agda`

**Interfaces:**
- CI checks only the canonical finite coupled modules and generated candidate module under `agda --safe`.

- [ ] Remove the external proof checkout from the acceptance path; retain no new Agda dependency.
- [ ] Remove unrelated economics and non-finite analytic checks from the canonical module.
- [ ] Run canonical source, canonical test, all three method modules, full coupling, and generated candidate module under `--safe`.
- [ ] Run generator and require all method × law candidates to be proven.
- [ ] Run the existing forbidden-theorem checker.

### Task 8: Review strict theorem ordering

**Files:**
- Create: `docs/dyadic-gru-theorem-order.md`

**Interfaces:**
- Documents only kernel-checkable algebraic implications and explicitly distinguishes strict structural dominance from statistical comparison.

- [ ] Establish flat > lazy/ladder only for one-step reachability and symmetry under all finite relabelings where those premises are represented.
- [ ] Establish Noisy Net recurrent representation dominance only through the explicit projection/lift theorem.
- [ ] Do not infer strict dominance from entropy, variance, or task performance.
- [ ] State the final theorem ordering as a partial order unless all required simulation/lift maps are present.
