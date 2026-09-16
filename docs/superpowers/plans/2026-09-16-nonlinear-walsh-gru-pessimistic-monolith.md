# Nonlinear, Walsh-Hadamard, GRU, and Pessimistic Monolith Refactor Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the legacy nonlinear/transform vocabulary with exact finite algebra, make the recurrent interface input-dependent with state-independent parameters, move the attention transform to an exactly orthonormal power-of-four Walsh-Hadamard basis, strengthen initialization and finite-cycle reasoning where the algebra actually permits it, and consolidate redundancy automation into Haskell.

**Architecture:** The canonical learner remains deterministic, actor-free, finite, and accepted only by `agda --safe`. Watkins remains the sole learned Q/action-selection source; learned sparsemax attention remains representation state. The transform layer becomes an exactly orthonormal normalized Walsh-Hadamard transform at dimensions `4^k`, so its normalization is dyadic rather than irrational. The old activation changes are implemented as exact finite definitions with explicit carriers and boundary proofs rather than string substitutions.

**Tech Stack:** Agda 2.8.0, Agda stdlib 2.4, Haskell for discovery/pruning, optional Guix/Nix environment declaration, GitHub Actions safe gate.

**Spec:** Current canonical source is `Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda`; shared recurrent source is `Exotic/ERL/FullCoupled/DyadicGRU.agda`; transform boundary is `Exotic/ERL/FullCoupled/FrozenOrthogonalAttentionGRU.agda`.

## Global Constraints

- No independently learned actor may be introduced.
- Learned sparsemax attention is representation state, not an actor.
- Watkins remains the only learned Q/action-selection source.
- All activation replacements must be mathematically defined in the finite carrier, not textual aliases.
- The recurrent update must depend on its current input; removing dependence on the input is forbidden by theorem gate.
- GRU parameters and persistent auxiliary coordinates must be state-independent under the step.
- Walsh-Hadamard dimensions are powers of four so exact normalization stays dyadic.
- Maximum pessimism must be defined relative to the critic's ordered semantic carrier, not guessed from raw modular `Int8` codes.
- Finite-cycle exclusion must come from a discharged Lyapunov/order theorem or exact finite dynamical invariant; initialization alone is not allowed to masquerade as a global no-cycle proof.
- The compositional Mobius theorem must remain an actual associativity theorem of `composeAction`, not a claim about unrelated transforms.
- The active negative q-log shaping variant may remain during the migration; its exact finite-rational value and signed control must stay distinct until a stronger composed theorem is proved.
- Remove obsolete pruning implementations instead of accumulating multiple audit scripts.
- New automation code is Haskell or declarative Guix/Nix. No new Bash/Python helper script is introduced.

---

### Task 1: Replace the recurrent nonlinear surface exactly

**Files:**
- Modify: `Exotic/ERL/FullCoupled/DyadicGRU.agda`
- Modify: `Exotic/ERL/FullCoupled/SignReLUSemidirectCycleComposition.agda`
- Modify: `Exotic/ERL/FullCoupled/SignReLUSemidirectCycleComposition_test.agda`
- Modify: `Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda`
- Modify: `.ci/discovery/ExplorationTheoremGenerator.hs`

**Interfaces:**
- Replace the current finite recurrent activation definition while preserving `gruStep` input dependence.
- Remove legacy activation theorem names from active canonical ownership.

- [ ] **Step 1: Define the finite semantic carrier for the quadratic activation.**

Use the signed integer interpretation already used by policy arithmetic. Define the activation semantically as `x * (1 - x)` on that carrier, then provide the explicit finite projection back to the recurrent coordinate carrier. Do not encode the replacement as an accidental modular `Int8` multiplication whose semantic range is unstated.

- [ ] **Step 2: Prove input dependence directly.**

Add a theorem witnessing two explicit inputs that produce different recurrent outputs for a fixed parameter/state configuration. The theorem must fail if the recurrent step becomes input-independent.

- [ ] **Step 3: Make recurrent parameters state-independent.**

Keep matrices, noise, and global control fixed across `gruStep`; only the hidden/input-dependent coordinate may change. State-independent means the parameter coordinates are not functions of the previous hidden state, not that the recurrent output ignores the input.

- [ ] **Step 4: Port the semidirect-window theorems to the new activation.**

Rename the active operator surface so that the semidirect theorem no longer asserts legacy activation terminology. Preserve exact operator associativity through `MobiusGroup.composeAction-assoc`.

- [ ] **Step 5: Add regression cases.**

Check zero input, a nonzero input, parameter persistence, and input separation under `--safe`.

---

### Task 2: Replace softsign surfaces with hard sign

**Files:**
- Modify every active Agda source containing a live softsign definition.
- Modify corresponding `_test.agda` sources.
- Modify `.ci/discovery/PruneRedundantComponents.hs`.

- [ ] **Step 1: Enumerate active definitions rather than relying on a repository-wide text replace.**

The code-search endpoint currently returns no complete softsign result on the feature branch, so ownership must be established from the branch tree and active imports before editing. A name occurrence in retired or generated documentation is not enough to establish a semantic replacement target.

- [ ] **Step 2: Define one finite hard-sign primitive.**

Use the existing signed Int8 semantic interpretation and define the sign result as the finite two-point carrier. Zero must be specified explicitly rather than inferred from a host-language comparison.

- [ ] **Step 3: Replace live softsign calls with the hard-sign primitive.**

Each replacement must preserve totality and expose a concrete regression theorem for negative, zero, and positive inputs.

- [ ] **Step 4: Extend the redundancy audit.**

The Haskell audit must flag duplicate activation definitions and stale softsign sources after migration.

---

### Task 3: Replace the frozen Haar boundary by exactly orthonormal normalized Walsh-Hadamard

**Files:**
- Modify: `Exotic/ERL/FullCoupled/FrozenOrthogonalAttentionGRU.agda`
- Modify: `Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda`
- Modify: corresponding canonical regression/test module.

**Interfaces:**
- Input vectors have dimension `4^k`.
- Transform is an exact normalized Walsh-Hadamard matrix over a dyadic finite/integer-scaled carrier.

- [ ] **Step 1: Establish the dimension invariant.**

Represent the dimension by `FourPower k = 4 ^ k` or an equivalent recursively defined finite dimension. Prove `sqrt (4 ^ k) = 2 ^ k` in the chosen exact carrier, so the normalization factor is dyadic.

- [ ] **Step 2: Define the base normalized transform.**

For dimension four use the exact `1/2` normalized Walsh-Hadamard basis. Do not use floating-point square roots.

- [ ] **Step 3: Define the recursive Kronecker/Walsh construction.**

The `4^k` transform must remain exact and orthonormal by construction. Prove row norm one and pairwise row orthogonality.

- [ ] **Step 4: Replace the canonical two-coordinate Haar lift with the smallest power-of-four embedding.**

Embed the two sparsemax coordinates into the canonical four-dimensional representation using explicit zero coordinates. The normalized transform must operate on the four-dimensional vector, preserving exact orthonormality.

- [ ] **Step 5: Add the strongest local theorem available.**

Prove `W W^T = I` for the active finite dimension and expose norm preservation for the canonical recurrent input projection. This is strictly stronger than the present `H H^T = 2I` result.

- [ ] **Step 6: Remove old Haar theorem ownership.**

Retire old `haarRow*`, unnormalised-transform definitions, and corresponding audit entries after the new transform passes `--safe`.

---

### Task 4: Identity initialization and semantically maximal pessimistic critic initialization

**Files:**
- Modify: `Exotic/ERL/FullCoupled/DyadicGRU.agda`
- Modify: `Exotic/ERL/FullCoupled/SparsemaxCriticWatkins.agda`
- Modify: `Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda`
- Modify: corresponding tests.

- [ ] **Step 1: Define identity initialization for nonlinear parameter blocks.**

Use explicit identity elements for every parameter block where the carrier has a genuine identity. Do not call a zero vector an identity unless the operation proves that it is the identity.

- [ ] **Step 2: Define critic semantic order.**

Introduce the ordered semantic critic carrier first. Then define `maxPessimisticCritic` as its least admissible semantic value, instead of assuming raw code zero is pessimistic under modular arithmetic.

- [ ] **Step 3: Prove initial pessimism.**

Prove that every admissible initial critic coordinate is above or equal to the chosen pessimistic initialization in the semantic order.

- [ ] **Step 4: Separate initialization from cycle exclusion.**

Do not claim that pessimistic initialization itself proves finite-cycle exclusion. Add a distinct monotonicity/invariant theorem. If the chosen initialization plus the update gives a global descending measure, discharge the resulting no-cycle theorem through `Int8StabilityComposition.noNontrivialFiniteCycle`.

---

### Task 5: Strengthen the whole connected no-actor composition theorem

**Files:**
- Modify: `Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda`
- Modify: `Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2_test.agda`
- Modify: `.ci/discovery/ExplorationTheoremGenerator.hs`
- Modify: `docs/THEOREM_FIRST_REPLICATION_WIKI.md`

- [ ] **Step 1: Preserve the actual canonical path.**

The active composition remains:

`Watkins critic -> deterministic LCB -> fixed-temperature sparsemax action-selection -> learner signal -> normalized Walsh-Hadamard -> input projection -> recurrent step`.

Learned sparsemax attention remains a separate representation state and is not relabeled as an actor.

- [ ] **Step 2: Prove composed persistent-coordinate preservation after the transform change.**

The theorem should instantiate the real canonical GRU step and prove preservation of matrices/noise/global controls after the exact normalized Walsh-Hadamard transformation.

- [ ] **Step 3: Prove norm preservation of the transformed recurrent input.**

Use the exact orthonormal theorem from Task 3 to establish a new finite norm-invariance boundary. This is a stronger algebraic result than the previous orthogonality-up-to-scale theorem.

- [ ] **Step 4: Prove the strongest finite-cycle theorem actually discharged by the new order/invariant.**

Possible outcomes are a global strict-descent no-cycle theorem or an exact invariant-fiber decomposition. Do not label either result as global convergence unless the proof actually establishes convergence.

- [ ] **Step 5: Keep Mobius associativity separate but composed.**

Expose the existing definitional associativity theorem and the new transform/recurrent composition theorem as separate lemmas inside one canonical theorem family. Neither theorem should falsely attribute associativity to Walsh-Hadamard multiplication.

---

### Task 6: Make the negative q-log scale endogenous and fully finite

**Files:**
- Modify: `Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda`
- Modify: canonical regression.

- [ ] **Step 1: Keep the exact finite-rational value separate from its Int8 control representation.**

The rational value remains a numerator/denominator pair. The signed control is an explicit finite parameter derived from learner state or fixed configuration, but the two must not be conflated.

- [ ] **Step 2: Define the scale as endogenous only through a proved state function.**

The scale may depend on canonical learner state, such as the finite policy/critic surface, only through a total definition whose codomain and boundedness are explicit.

- [ ] **Step 3: Prove finite totality and composition.**

Show the scale is defined for every canonical state and the q-log shaping signal is total over the finite carrier.

- [ ] **Step 4: Keep the model free of posterior semantics.**

No Bayesian interpretation, continuous-log identity, or statistical claim is added merely because the shaping factor is called q-log.

---

### Task 7: Consolidate redundancy pruning into the existing Haskell audit

**Files:**
- Modify: `.ci/discovery/PruneRedundantComponents.hs`
- Modify: `.github/workflows/agda.yml`
- Delete obsolete pruning-only scripts once usage is verified.

- [ ] **Step 1: Extend the existing audit instead of adding another language/tool.**

Audit q-log, action-selection, learned attention, Walsh-Hadamard, recurrent nonlinearities, GRU, LCB, optimizer, full-step, and retired source paths from one Haskell program.

- [ ] **Step 2: Add explicit stale-token families.**

The audit must flag legacy signReLU, softsign, unnormalised-Haar, duplicate action/actor surfaces, duplicate q-log implementations, and retired component modules.

- [ ] **Step 3: Keep pruning non-destructive by default.**

The audit reports a path for retirement and exits nonzero; source deletion remains a separate reviewed Git operation.

- [ ] **Step 4: Remove superseded standalone pruning scripts.**

Delete only scripts that are actually redundant with the consolidated Haskell audit and no longer referenced by CI or documentation.

---

### Task 8: Reproducible environment without new shell helper code

**Files:**
- Create: `flake.nix` and/or `guix.scm` only if the repository does not already contain an equivalent environment declaration.
- Modify: `.github/workflows/agda.yml` only to consume the declarative environment or existing setup action.

- [ ] **Step 1: Pin Agda and stdlib versions in the declarative environment.**

Match the current CI versions: Agda 2.8.0 and stdlib 2.4.

- [ ] **Step 2: Pin the Haskell compiler needed by the generator.**

Use the existing supported GHC release used by CI, and keep generator execution in `.hs` rather than introducing a shell wrapper.

- [ ] **Step 3: Remove new Bash/Python helper logic.

All repository automation introduced by this refactor must remain Agda, Haskell, or declarative environment configuration.

---

### Task 9: Final theorem/report gate

**Files:**
- Modify: `.ci/discovery/ExplorationTheoremGenerator.hs`
- Modify: `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`
- Modify: `.github/workflows/agda.yml`
- Modify: `docs/THEOREM_FIRST_REPLICATION_WIKI.md`

- [ ] **Step 1: Require the new normalized-Walsh, activation, input-dependence, pessimistic-order, q-log, and cycle theorems.**

The generator must mark the family `Proven` only when all named proof terms exist and the complete canonical source succeeds under `agda --safe`.

- [ ] **Step 2: Add regression declarations that distinguish representation attention from action selection.**

The generated report must never imply that learned sparsemax attention is an independently trained actor.

- [ ] **Step 3: Update the theorem-first wiki only after the new source compiles.**

State exact proven identities and explicit non-claims. Do not promote proposed stronger theorems merely because their intended definitions exist.

- [ ] **Step 4: Run the full safe gate.**

Run the unified redundancy audit, all active component modules, canonical regression, generated theorem report, count-memory theorem, semidirect theorem, and persistent-GRU bridge.

---

## Expected theorem gains

The mathematically strongest low-risk gain is the normalized Walsh-Hadamard result at dimension `4^k`: exact orthonormality and norm preservation with dyadic normalization. The composed persistent-GRU theorem is also strengthened because it can be instantiated after that exact transform. A strictly stronger finite-cycle theorem is conditional on finding a discharged monotone measure/invariant for the *new* update. Pessimistic initialization alone does not imply absence of cycles, and Mobius associativity alone does not imply absence of cycles.

The current repository already has `canonicalPersistentGRUPreservation` and `mobiusAssociativity`; the refactor should preserve and strengthen their composition rather than duplicate them.
