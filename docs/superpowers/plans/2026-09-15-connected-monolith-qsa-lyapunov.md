# Connected GRU/QSA Monolith Lyapunov Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the placeholder-level component certificates with one connected theorem proving the hidden/persistent semidirect decomposition, a whole-coupling Lyapunov law, and finite deterministic QSA convergence/cycle-freedom at the same monolithic state boundary.

**Architecture:** Represent the persistent GRU carrier by its endomorphism monoid and let it act by reindexing a persistent-indexed family of hidden endomorphisms. Encode a concrete `GRUState` into this nontrivial semidirect product and prove the exact `gruStep` law. Build one combined GRU+QSA state transition and one Nat-valued monolithic energy; optimizer/L2/path/L1 components are audited in the same theorem instead of receiving independent cycle theorems.

**Tech Stack:** Agda 2.8.0, stdlib 2.4, `--safe`, finite Int8/dyadic carriers.

**Spec:** `docs/THEOREM_FIRST_REPLICATION_WIKI.md` plus the existing finite-cycle and deterministic-QSA modules.

## Global Constraints

- Agda `--safe` is the mathematical authority.
- No postulates, unsafe features, Float/Real imports, or empirical/environment-dependent convergence claims.
- No placeholder `refl` certificates may be presented as optimization, norm, CHAD, or Markov results.
- The theorem must operate on the connected state, not on isolated subsystem projections.
- A deterministic QSA theorem requires a concrete step map, strict Lyapunov witness, decidable equality, and unique terminal fixed point.
- Noisy support relations may not inherit deterministic strict Lyapunov descent automatically.

---

### Task 1: Prove the nontrivial hidden/persistent semidirect embedding

**Files:**
- Create: `Exotic/ERL/FullCoupled/ConnectedGRUSemidirectQSA.agda`
- Modify: `Exotic/ERL/FullCoupled/SignReLUSemidirectCycleComposition_test.agda`

**Interfaces:**
- `PersistentGRU = GRUMatrices × (GRUNoise × GlobalControl)`.
- `EndoPersistent` is the monoid of endomorphisms of `PersistentGRU`.
- `HiddenFamily = PersistentGRU → MobiusAction` with pointwise operator composition.
- `HiddenFamilyAction` reindexes a hidden family by an `EndoPersistent` action.
- `hiddenPersistentSemidirect : Semidirect HiddenFamily EndoPersistent`.
- `encodeGRU`, `decodeGRU`, and `gruStepSemidirectEmbedding` encode the actual `gruStep` exactly.

- [ ] Define reverse-composition monoids for `EndoPersistent` and `HiddenFamily`.
- [ ] Prove the reindexing action unit, multiplicative, and endomorphism laws.
- [ ] Encode a state as a constant hidden endomorphism paired with a constant persistent endomorphism.
- [ ] Decode by evaluating the persistent endomorphism at a fixed base carrier and the hidden endomorphism at a fixed hidden base point.
- [ ] Define the fixed semidirect element for each concrete Int8 input and prove decoded multiplication equals `gruStep`.
- [ ] Add regression lemmas asserting that persistent coordinates remain unchanged under the embedded step.

### Task 2: Prove the whole-coupling energy theorem

**Files:**
- Modify: `Exotic/ERL/FullCoupled/ConnectedGRUSemidirectQSA.agda`

**Interfaces:**
- `ConnectedQSAState` is a finite Int8 QSA state.
- `ConnectedMonolithState = GRUState × ConnectedQSAState`.
- `connectedStep` composes actual `gruStep` with a concrete QSA step supplied by the same connected state transition.
- `WholeCouplingEnergy` combines hidden, QSA, optimizer, L2, path-norm, and L1 contributions into one Nat-valued energy.
- `WholeCouplingLyapunov` carries one strict-decrease law for the complete transition.

- [ ] Prove optimizer-token, L2-token, and persistent-carrier contributions are invariant inside the connected step.
- [ ] Keep path-norm and L1 as explicit finite functions of the actual learned carrier; do not create fake numerical inequalities.
- [ ] Prove the combined energy theorem directly on `ConnectedMonolithState`.
- [ ] Prove that every non-fixed connected transition has a genuine strict source among the changing dynamic coordinates, rather than claiming that every component decreases.
- [ ] Prove arbitrary-n finite-cycle exclusion for the monolithic transition from this single whole-coupling Lyapunov certificate.
- [ ] Add an audit theorem identifying exactly which contributions are zero/invariant and which are responsible for strict descent under the supplied certificate.

### Task 3: Connect the existing deterministic QSA convergence proof

**Files:**
- Modify: `Exotic/ERL/FullCoupled/DeterministicQSA.agda`
- Modify: `Exotic/ERL/FullCoupled/DeterministicQSA_test.agda`

- [ ] Reuse `deterministicQSAStyleConvergence` and `deterministicQSAStyleNoNontrivialCycle` rather than duplicating cycle logic.
- [ ] Add a monolithic corollary in which the QSA state is part of the connected coupling and the same whole-state Lyapunov certificate is consumed.
- [ ] State explicitly that the theorem is deterministic finite QSA-style convergence, not a classical stochastic-approximation convergence theorem.
- [ ] Do not upgrade the QSA result until the concrete connected QSA update is shown to satisfy the supplied whole-state certificate.

### Task 4: Prune unsupported certificate surfaces from the connected theorem path

**Files:**
- Modify or remove any connected-path imports of `LearnedRegularizationComposition.agda`, `SparsemaxF4Composition.agda`, `TheoremVariantComparison.agda`, or other files whose claims are only reflexive interface equalities.
- Modify: `.github/workflows/agda.yml`

- [ ] Ensure the connected monolith theorem imports only kernel-proven algebra and actual state transition laws.
- [ ] Do not delete unrelated historical modules unless no active path references them.
- [ ] Remove workflow checks that merely certify placeholder interfaces as substantive optimization/norm/CHAD theorems.
- [ ] Add the connected monolith module and test to the authoritative Agda gate.

### Task 5: Validate and review

- [ ] Run `agda --safe` on the new monolith and test modules.
- [ ] Run the existing deterministic QSA modules under `--safe`.
- [ ] Poll GitHub Actions for the exact PR head SHA and do not label the branch green without a fresh successful run.
- [ ] Review the final theorem dependency graph: whole-state Lyapunov -> arbitrary-n cycle exclusion -> deterministic QSA convergence, with no component-level cycle theorem treated as the main result.
