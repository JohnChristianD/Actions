# Canonical Ergodic Learner + EA Composition Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make Agda `--safe` prove the strongest valid aperiodicity theorem directly on the composed learner/EA transition, then replace the incomplete MR15 mutation shell with a finite, fully specified modified-MR15 exploration layer whose global reachability is either proved constructively or exposed as an explicit finite obligation.

**Architecture:** Separate graph-theoretic facts from learner semantics. First define finite transition paths and prove that global irreducibility plus one full-state self-loop implies aperiodicity without any causality premise. Then define a complete modified-MR15 generation transition carrying population, parent selection, mean update, corrected one-fifth step-size adaptation, neutral mutation, and a faithful `CanonicalLearner.step`. Finally expose the combined state-transition relation and prove product/composition theorems wherever the actual transition is sufficient; unsupported global learner reachability remains an explicit obligation, never a fabricated inhabitant.

**Tech Stack:** Agda 2.8.0, Agda standard library 2.4, `--safe`, existing finite Int8/dyadic primitives.

**Spec:** `docs/superpowers/specs/2026-09-13-canonical-dyadic-exploration-design.md`

## Global Constraints

- Agda `--safe` is the sole mathematical authority.
- No `postulate`, `--unsafe`, probabilistic oracle, Clojure/Haskell/Elixir proof oracle, or generated proof shortcut.
- D_tri remains the sole explicit stochastic noise law: 31-point triangular weights `1..16..1` over total weight 256.
- No Gaussian, softmax, Munchausen, Tsallis-2, or True Online TD in the canonical learner.
- The canonical learner remains finite Int8/dyadic and its actual `step` function is the transition used in reachability claims.
- Aperiodicity is proved from the full composed transition relation; causality equivalence is not an input to the theorem.
- MR15 is canonical only if its stronger finite-lattice exploration property is actually supported by the composed transition; otherwise retain the stronger proven Noisy-Net result.

---

### Task 1: Direct graph-theoretic aperiodicity theorem

**Files:**
- Create: `Exotic/ERL/FullCoupled/FiniteAperiodicity.agda`
- Modify: `Exotic/ERL/FullCoupled/CanonicalErgodicity.agda`
- Modify: `.github/workflows/agda.yml`

**Interfaces:**
- `Step {S} : S -> S -> Set` is an abstract transition relation.
- `Path Step n x y` is an exact-length path.
- `Reach Step x y` is reflexive/transitive reachability derived from paths.
- `AperiodicViaCoprimeReturns Step x` is witnessed by positive return paths of consecutive lengths `n` and `suc n`.
- `irreducible-plus-selfLoop-implies-aperiodic` proves every state is aperiodic when every state can reach and return from a hub that has a one-step self-loop.

- [ ] Define `Path` and `Reach` without referencing causality, online/replay equivalence, or exploration-only relations.
- [ ] Define `AperiodicViaCoprimeReturns` using two positive return lengths `n` and `suc n`, so no gcd library theorem is needed to establish coprimality.
- [ ] Prove path concatenation and the return-length construction through a hub self-loop.
- [ ] Lift the theorem to `CanonicalErgodicity` using the actual `CanonicalLearner.step` relation.
- [ ] Add the module to the safe workflow.

### Task 2: Fully specified modified MR15 finite EA

**Files:**
- Create: `Exotic/ERL/Exploration/CanonicalMR15GA.agda`
- Modify: `.github/workflows/agda.yml`

**Interfaces:**
- `Genome = Fin dimension -> Fin 256` with `dimension = 4` and population size 16.
- `Population = Fin populationSize -> Genome`.
- Deterministic `fitness`, ranking, `topQuarter`, `meanGenome`, and `mutatedGeneration`.
- Corrected neutral one-fifth step-size update represented only with natural-number comparisons; no literal irrational/floating arithmetic.
- Unit mutation uses the actual D_tri `pos`, `neg`, and `zero` witnesses.
- `MR15Generation` contains population, current mean, exponent, and success count.

- [ ] Replace the mutation-only skeleton with a complete finite generation operator.
- [ ] Make selection deterministic by a total finite ranking function and prove selected indices are in range.
- [ ] Define the population mean with exact integer division and a deterministic tie-break rule.
- [ ] Define the corrected one-fifth update and prove the below/above threshold cases.
- [ ] Prove no-perturb and zero-noise generation self-loops for a neutral generation.
- [ ] Prove that a unit mutation changes exactly one genome coordinate by `+1` or `-1` modulo 256.

### Task 3: Full learner + EA composition

**Files:**
- Create: `Exotic/ERL/FullCoupled/CanonicalLearnerEA.agda`
- Modify: `.ci/canonical-module.txt`
- Modify: `.github/workflows/agda.yml`

**Interfaces:**
- `CoupledState = LearnerState × MR15Generation`.
- `coupledStep` invokes the real `CanonicalLearner.step` and the real `CanonicalMR15GA.generationStep` in one transition.
- `CoupledReach` is exact reachability of `coupledStep`, not a product of unrelated relations.
- `coupledSelfLoop` is proved at the actual neutral starting state.
- `CoupledIrreducibilityObligation` quantifies over the full composed state space.

- [ ] Define the coupled state and one-step transition with no causal shortcut.
- [ ] Prove the neutral full-state self-loop using the existing learner witness plus the EA neutral mutation/generation witness.
- [ ] Prove projections from a coupled path to learner and EA paths.
- [ ] Prove a conditional product theorem: independent component reachability plus synchronized neutral-step witnesses implies coupled reachability where the transition definition actually permits it.
- [ ] Keep full coupled irreducibility as an obligation until the actual learner transition is shown to generate every learner-state coordinate.

### Task 4: Lattice reachability closure

**Files:**
- Modify: `Exotic/ERL/FullCoupled/CanonicalLearnerEA.agda`
- Create: `Exotic/ERL/FullCoupled/LatticeReachability.agda`

- [ ] Prove finite-coordinate reachability for the EA genome lattice using repeated unit mutation and coordinate sequencing.
- [ ] Prove the finite population lattice is reachable under the actual generation relation only where selection/mean update preserves the constructive unit-move path; otherwise state the exact residual obligation.
- [ ] Classify learner-state reachability coordinate-by-coordinate: exact proof, conditional proof, or unresolved obligation.
- [ ] Define the strongest honest full-chain theorem as the conjunction of the proven EA lattice theorem, learner reachability obligation, and composed self-loop.

### Task 5: Exploration choice theorem and canonical switch

**Files:**
- Modify: `docs/superpowers/specs/2026-09-13-canonical-dyadic-exploration-design.md`
- Modify: `.github/workflows/agda.yml`
- Modify: `.ci/canonical-module.txt`

- [ ] Compare Noisy Nets and MR15 using formal properties actually proved in Agda: support dimensionality, direct lattice moves, full-state self-loop availability, and composed-chain reachability obligations.
- [ ] Switch the canonical exploration mechanism to MR15 only after the theorem comparison is kernel-checked.
- [ ] Ban the previous canonical exploration mechanism from canonical files only after the switch is complete and all canonical tests pass.
- [ ] Never claim “better” from empirical intuition alone; record the formal criterion and exact theorem that justifies the choice.

### Task 6: Safe CI closure

**Files:**
- Modify: `.github/workflows/agda.yml`
- Modify: `.ci/canonical-module.txt`

- [ ] Check every new canonical module with `agda --safe`.
- [ ] Keep `postulate`, `--unsafe`, and banned mechanisms rejected.
- [ ] Require the composed learner+EA module and theorem modules in the canonical safe gate.
- [ ] Treat GitHub Actions output, not this plan, as the final verification of the current head.
