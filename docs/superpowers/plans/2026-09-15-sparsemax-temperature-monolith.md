# Sparsemax Fixed-Temperature Endogenous Monolith Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the actual finite learner a single generated Agda monolith with a fixed Int8-dyadic sparsemax policy temperature `1/8`, Watkins-only learned critic semantics, corrected signed finite-rational q-log shaping plus deterministic LCB exploration, persistent GRU and frozen Haar sandwich, norm-pair state, and global optimizer with an explicit coercive quadratic-decay theorem boundary.

**Architecture:** The canonical learner remains deterministic and finite. Sparsemax policy is a fixed-temperature map from the Watkins critic/LCB score surface and is not a separately learned actor; the independent attention/representation coordinates remain inside the learner state and are optimized by the same global optimizer. The monolith exposes exact one-step definitions, component-composition equalities, norm/regularizer coupling, finite rational q-log/LCB laws, and safe theorem certificates. The Haskell theorem generator is repointed from retired exploration methods to the monolith and emits a generated Agda theorem-status module that CI checks with `agda --safe`.

**Tech Stack:** Agda 2.8.0, Agda standard library 2.4, existing `Exotic/efficient_chad/Int8.agda` finite carrier, existing Haskell `ExplorationTheoremGenerator.hs`, GitHub Actions safe gate.

**Spec:** This plan is the canonical implementation specification for the fixed-temperature sparsemax and endogenous learner monolith requested in the 2026-09-15 session.

## Global Constraints

- Keep the learner deterministic and finite; do not reintroduce probabilistic/posterior semantics.
- Keep Watkins as the only learned critic/policy source; no separate learned actor state.
- Sparsemax policy temperature is fixed at exactly `1/8`, represented as the Int8 dyadic code `16/128`.
- Preserve the independent learned attention/representation component and the frozen unnormalised Haar sandwich between attention and recurrent input.
- Preserve corrected negative finite-rational q-log shaping semantics and deterministic count-memory LCB exploration.
- Preserve persistent signReLU GRU, norm-pair state, F4 global optimizer, and actual coupled L2 term.
- The quadratic-decay theorem may use an explicit finite coercive witness, but no theorem may claim a property not discharged by `--safe` Agda terms.
- Haskell only generates candidate theorem-status source; Agda remains the acceptance oracle.
- Update the repository's theorem-first wiki ledger in `docs/THEOREM_FIRST_REPLICATION_WIKI.md` because the live GitHub Wiki endpoint is not writable through the connected GitHub tool.

---

### Task 1: Replace retired theorem-generator targets with the canonical monolith

**Files:**
- Modify: `.ci/discovery/ExplorationTheoremGenerator.hs`
- Modify: `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`

**Interfaces:**
- Consumes: `Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith.agda` and its named theorem terms.
- Produces: generated learner theorem status for the canonical monolith.

- [ ] **Step 1: Write the generator metadata for the monolith.**

Use one theorem-family record for the monolith and require concrete symbols for: `sparsemaxTemperature`, `temperatureScaledSparsemax`, `sparsemaxTemperatureLaw`, `lcbSparsemaxPolicy`, `qLog2`, `negativeFiniteRationalQLog`, `haarOrthogonality`, `persistent-preservation`, `f4ParameterInvariant`, `normPair`, `fullStep`, and `fullCoupledQuadraticDecay`.

- [ ] **Step 2: Remove references to retired exploration modules from the generator.**

The generator must no longer require `MR15Reachability.agda`, `OpenESDyadic.agda`, or `NoisyNetCoupled.agda`.

- [ ] **Step 3: Keep Agda as the acceptance oracle.**

Retain the existing pattern: source-symbol presence check followed by `agda --safe` and generated status output.

- [ ] **Step 4: Update generated output.**

The generated module must report only the canonical monolith theorem family and fail the generator if any required proof symbol is absent or the monolith fails `agda --safe`.

- [ ] **Step 5: Commit the generator change.**

```bash
git add .ci/discovery/ExplorationTheoremGenerator.hs Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda
git commit -m "ci: generate canonical learner theorem status"
```

---

### Task 2: Add fixed Int8-dyadic sparsemax policy temperature

**Files:**
- Modify: `Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith.agda`
- Modify: `Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith_test.agda`

**Interfaces:**
- Consumes: `ActionScore`, `Int8`, Watkins critic scores, LCB-adjusted scores.
- Produces: `sparsemaxTemperature`, `temperatureScaledSparsemax`, exact fixed-temperature policy laws.

- [ ] **Step 1: Define the exact temperature code.**

Use the fixed Q7 Int8-dyadic code `16`, representing `16/128 = 1/8`, and keep it outside the learned state.

```agda
sparsemaxTemperature : Int8
sparsemaxTemperature = int8OfNat 16
```

- [ ] **Step 2: Define signed score interpretation without changing the underlying Int8 carrier.**

Use a centered signed lift for policy-score arithmetic so finite-rational differences do not wrap modulo 256 during theorem calculations.

- [ ] **Step 3: Define the exact two-action temperature-scaled sparsemax map.**

For signed Q7 score difference `d`, define the left weight in Q7 units as the clipped value of `(128 + 128*d/16)/2`; avoid host floating point and prove the finite arithmetic directly.

- [ ] **Step 4: Prove fixed-temperature laws.**

Prove exact tie, support, simplex-mass, nonnegativity, and one-hot saturation cases. Include a theorem that the temperature constant is definitionally fixed and not a learned parameter.

- [ ] **Step 5: Route Watkins-only policy construction through the fixed-temperature map.**

`lcbSparsemaxPolicy` and `scheduledSparsemaxPolicy` must call the fixed-temperature sparsemax function. No actor state is introduced.

- [ ] **Step 6: Add concrete regression terms for temperature `1/8`.**

Test tie, positive difference, negative difference, and saturation at the exact Int8 code boundary.

- [ ] **Step 7: Commit.**

```bash
git add Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith.agda Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith_test.agda
git commit -m "feat: fix sparsemax policy temperature at one eighth"
```

---

### Task 3: Restore the corrected finite-rational negative q-log + LCB composition

**Files:**
- Modify: `Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith.agda`
- Modify: `Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith_test.agda`

**Interfaces:**
- Consumes: signed finite-rational Int8 lift, fixed sparsemax policy, LCB count state.
- Produces: exact deterministic shaped critic scores used by the pseudo-actor policy.

- [ ] **Step 1: Add an explicit finite-rational signed carrier boundary.**

Represent the signed Int8 semantic value separately from modular code arithmetic. The negative operation must map a positive finite-rational code to its exact additive inverse in the theorem carrier rather than relying on modular `256 - code` as the semantic definition.

- [ ] **Step 2: Implement q-log as `1 - 1/x` in the finite-rational carrier.**

Preserve the corrected finite algebra shape from the older safe port, but avoid importing the retired generic module. The actual target is a local finite-rational theorem surface used by the monolith.

- [ ] **Step 3: Compose the negative q-log correction with the Int8 LCB bonus.**

The order must be deterministic and explicit: critic score -> q-log shaping -> count correction -> fixed-temperature sparsemax.

- [ ] **Step 4: Prove the composition equalities.**

Provide definitional or direct propositional equalities for the score pipeline and prove that the LCB counter transition is driven only by the resulting policy output.

- [ ] **Step 5: Add regression terms covering zero-count and saturated-count LCB cases.**

Use the existing finite LCB sequence `127,63,31,15,7,3,1,0` and prove the corresponding corrected policy input is total.

- [ ] **Step 6: Commit.**

```bash
git add Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith.agda Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith_test.agda
git commit -m "feat: compose finite qlog and count exploration"
```

---

### Task 4: Make the learner state genuinely monolithic

**Files:**
- Modify: `Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith.agda`
- Modify: `Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith_test.agda`

**Interfaces:**
- Consumes: attention, sparsemax policy, LCB, Watkins, GRU, Haar, optimizer, norm-pair components.
- Produces: one `FullCoupledState` endofunction with component composition laws.

- [ ] **Step 1: Extend `FullCoupledState` with the independent learned attention representation.**

The attention representation must remain distinct from the Watkins critic state, while both are inside one monolithic state and share the global optimizer state.

- [ ] **Step 2: Add the frozen Haar transform at the exact boundary.**

The current `FrozenOrthogonalAttentionGRU.agda` proves `HH^T = 2I` but is currently an interface-only layer. Import its exact transform into the monolith and prove that the recurrent input is the transformed attention output.

- [ ] **Step 3: Preserve persistent GRU coordinates.**

Connect the transformed attention signal to the existing `gruStep` and retain the exact `persistent-preservation` theorem.

- [ ] **Step 4: Keep Watkins critic-only learning.**

No actor parameters or actor optimizer state may enter the monolithic carrier. The sparsemax policy is computed from the critic/LCB score surface only.

- [ ] **Step 5: Expose exact one-step composition laws.**

Add named equalities showing that `fullStep` simultaneously advances clock, critic/Watkins, sparsemax-derived exploration counts, GRU, optimizer, norm-pair, and attention state.

- [ ] **Step 6: Commit.**

```bash
git add Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith.agda Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith_test.agda
git commit -m "feat: compose the full learner monolith"
```

---

### Task 5: Add norm-pair and global coercive quadratic-decay theorem boundary

**Files:**
- Modify: `Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith.agda`
- Modify: `Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith_test.agda`

**Interfaces:**
- Consumes: `NormPair`, `F4IntUState`, global L2 term, complete `fullStep`.
- Produces: explicit finite `fullCoupledQuadraticDecay` theorem used by the Haskell generator.

- [ ] **Step 1: Define the coupled quadratic energy.**

Use a finite Nat-valued witness built from the exact optimizer coordinates plus the `l1` and `path` norm-pair components. The energy must visibly contain the global L2 contribution rather than merely carrying it as an unused parameter.

- [ ] **Step 2: State the coercive decay condition on the actual update.**

For non-fixed learner states, require strict energy decrease under the exact global optimizer step. The theorem must apply to `fullStep`, not to a detached optimizer-only function.

- [ ] **Step 3: Prove the monolithic decay theorem for the concrete finite witness.**

Do not introduce a bare certificate field named as a theorem. The proof term must derive the final theorem from the finite definitions and the explicit coercive witness assumptions actually required by the algebra.

- [ ] **Step 4: Compose the decay theorem with the existing no-nontrivial-cycle theorem.**

Use `Int8StabilityComposition.noNontrivialFiniteCycle` only after the monolithic strict-decrease theorem is established.

- [ ] **Step 5: Add regression coverage for fixed versus strictly moved states.**

Show that fixed points are not required to decrease while every state covered by the coercive witness and moved by the real one-step map does.

- [ ] **Step 6: Commit.**

```bash
git add Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith.agda Exotic/ERL/FullCoupled/SparsemaxWatkinsMonolith_test.agda
git commit -m "proof: add monolithic coercive quadratic decay"
```

---

### Task 6: Update the safe CI gate and generated theorem target

**Files:**
- Modify: `.github/workflows/agda.yml`
- Modify: `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`

**Interfaces:**
- Consumes: canonical monolith and generator output.
- Produces: CI that directly checks the generated theorem surface and all required component modules.

- [ ] **Step 1: Keep the component checks.**

The gate must continue to check Int8, fixed-temperature sparsemax, Haar sandwich, Watkins critic-only layer, monolith, regression, stability theorem, signReLU semidirect composition, and persistent GRU bridge.

- [ ] **Step 2: Add the Haskell generator execution.**

Run the existing Haskell generator before the generated Agda module is checked, so generation is exercised rather than merely checked as a stale artifact.

- [ ] **Step 3: Check the generated Agda theorem report under `--safe`.**

The generated report must itself be a CI input and all required statuses must be `Proven`.

- [ ] **Step 4: Commit.**

```bash
git add .github/workflows/agda.yml Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda
 git commit -m "ci: gate generated canonical learner theorems"
```

---

### Task 7: Replace the stale theorem-first wiki ledger with the canonical architecture

**Files:**
- Modify: `docs/THEOREM_FIRST_REPLICATION_WIKI.md`

**Interfaces:**
- Consumes: current canonical monolith and CI paths.
- Produces: authoritative theorem-first component ledger.

- [ ] **Step 1: Replace retired exploration architecture.**

Remove references to the old three-method exploration comparison as the current canonical learner.

- [ ] **Step 2: Document canonical components explicitly.**

The ledger must list: independent learned sparsemax attention; fixed `1/8` Int8-dyadic sparsemax pseudo-actor policy; Watkins-only critic; negative finite-rational q-log shaping; deterministic LCB count exploration; frozen unnormalised Haar sandwich; persistent signReLU GRU; norm-pair; global F4 optimizer; coercive quadratic energy; Nat clock; generated theorem status.

- [ ] **Step 3: Document theorem boundaries honestly.**

State that `--safe` Agda proof terms, not Haskell generation or literature claims, are the acceptance oracle. Do not claim general stochastic convergence, posterior semantics, or equilibrium results.

- [ ] **Step 4: Commit.**

```bash
git add docs/THEOREM_FIRST_REPLICATION_WIKI.md
git commit -m "docs: canonize endogenous learner theorem components"
```

---

### Task 8: Whole-branch safe review and CI verification

**Files:**
- No new files. Review the complete branch.

- [ ] **Step 1: Run the repository-safe gate.**

Use the existing GitHub Actions workflow as the authoritative compiler/test environment.

- [ ] **Step 2: Inspect the generated theorem report.**

Confirm every required monolith theorem status is `Proven` and no stale retired method appears.

- [ ] **Step 3: Verify the PR head and changed-file surface.**

Confirm the new monolith and generator are on `signrelu-semidirect-cycle-main` and the PR remains mergeable.

- [ ] **Step 4: Publish the final status in the PR.**

Add one concise issue comment documenting the exact theorem boundary and the CI result; do not claim green until GitHub reports a successful workflow run.

- [ ] **Step 5: Final review.**

Check that fixed temperature is a definition, not a parameter; no actor state exists; the monolith consumes all requested components; generation is exercised by CI; and the wiki ledger matches the actual checked source tree.
