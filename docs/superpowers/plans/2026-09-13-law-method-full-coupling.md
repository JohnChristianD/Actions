# Law-Method Full-Coupling Theorem Permutations Implementation Plan

> **For agentic workers:** theorem generation is endogenous: actual explorer × retained dyadic law × representation boundary, with Agda `--safe` as the acceptance oracle.

**Goal:** Make the exploration theorem generator emit only endogenous theorem artifacts for every actual explorer paired with the single retained Flat Dyadic probability law after full algebraic coupling composition.

**Architecture:** `DyadicLaw` is a finite law tag plus exact normalization/support facts. Actual explorer modules remain MR15, OpenES, and coupled Noisy Nets. `FullAlgebraicCoupling` is the theorem boundary that composes one actual explorer with Flat Dyadic and derives `PeriodOne` only from the composed proof object. The representation boundary is `softsignQ8 (signReLUQ8 x)`; Noisy Nets additionally has an explicit projection/lift theorem connecting its full coupled state to that quotient.

**Tech Stack:** Agda `--safe`, Haskell `runghc` generator, GitHub Actions.

**Spec:** The existing theorem-first exploration surface and current PR #27.

## Global Constraints

- Canonical mathematical authority is Agda `--safe`.
- Actual exploration methods are MR15, OpenES, and coupled Noisy Nets.
- Flat Dyadic is the only selectable probability-law module.
- Lazy Walk and Dyadic Ladder are pruned from the active theorem surface.
- The legacy triangular law is pruned and guarded against reintroduction.
- No empirical/data analysis is introduced.

---

### Task 1: Define the retained law and full theorem boundary

**Files:**
- `Exotic/ERL/Exploration/FlatDyadic.agda`
- `Exotic/ERL/Exploration/DyadicLaw.agda`
- `Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda`

- [x] Flat Dyadic is uniform over all 256 Int8 codes with exact denominator 256.
- [x] Prove normalization, zero support, ±1 support, and universal positive support.
- [x] Make `DyadicLaw` contain only `flatDyadic`.
- [x] Make `FullAlgebraicCoupling` carry normalization, unit support, universal support, representation forward/pullback laws, explorer irreducibility, self-loop, and derived period one.

### Task 2: Generate the endogenous frontier

**Files:**
- `.ci/discovery/ExplorationTheoremGenerator.hs`
- `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`

- [x] Enumerate MR15, OpenES, and Noisy Nets against Flat Dyadic only.
- [x] Emit exactly three `Endogenous` theorem objects through `composeFull`.
- [x] Pass both unit and universal support proofs into the theorem boundary.
- [x] Keep Haskell as source generation only; Agda `--safe` is the acceptance oracle.

Expected theorem names:
`MR15FlatDyadicEndogenous`, `OpenESFlatDyadicEndogenous`, `NoisyNetFlatDyadicEndogenous`.

### Task 3: Connect Noisy Nets to the representation layer

**Files:**
- `Exotic/ERL/Finite/Activation.agda`
- `Exotic/efficient_chad/SoftsignGatedComposition.agda`
- `Exotic/ERL/FullCoupled/NoisyNetRepresentationProjection.agda`

- [x] Concrete finite forward functions are `signReLUQ8` and `softsignQ8`.
- [x] The representation observable is `softsignQ8 (signReLUQ8 x)`.
- [x] Prove projection/section for the Noisy-Net coupled state.
- [x] Prove every representation step lifts into the coupled Noisy-Net relation.
- [x] Prove every coupled Noisy-Net step projects to the representation relation.
- [x] Prove representation irreducibility, self-loop, and period one.
- [x] Prove full coupled Noisy-Net irreducibility and self-loop.
- [x] Exhibit distinct GateParams in one representation fiber, establishing a genuine strict state extension.

Concrete activation-specific Möbius closure remains conditional on concrete in-tree Möbius witnesses; generic CHAD composition does not fabricate them.

### Task 4: Strict theorem ordering

- [x] Retained Flat Dyadic is maximal in the law-support theorem class because every Int8 code has positive one-step support.
- [x] Noisy-Net is strictly above the softsign-gated quotient theorem because the quotient has a section, every coupled step projects/lifts through the boundary, and distinct hidden GateParams collapse to the same representation signal.
- [ ] MR15 production-state projection/lift theorem.
- [ ] OpenES production-state projection/lift theorem.

Until the last two are kernel-checked, do not assign a false strict cross-method ordering against Noisy Nets.

### Task 5: CI acceptance

- [x] Remove obsolete law-module workflow checks for the pruned variants.
- [x] Add retained Flat Dyadic, full coupling, softsign-gated composition, and Noisy-Net projection checks.
- [ ] Require a fresh green run after the latest head is pushed.
