# Law-Method Full-Coupling Theorem Permutations Implementation Plan

> **For agentic workers:** theorem generation is endogenous: actual explorer × retained dyadic law × representation boundary, with Agda `--safe` as the acceptance oracle.

**Goal:** Make the exploration theorem generator emit only endogenous theorem artifacts for every actual explorer paired with the single retained Flat Dyadic probability law after full algebraic coupling composition.

**Architecture:** `DyadicLaw` is a finite law tag plus exact normalization/support facts. Actual explorer modules remain MR15, OpenES, and coupled Noisy Nets. `FullAlgebraicCoupling` is the theorem boundary that composes one actual explorer with Flat Dyadic and derives `PeriodOne` only from the composed proof object. The canonical exploration boundary is `SoftsignGatedRepresentation`; the scalar explorer is a quotient of that representation and the coupled explorer is a strict state extension through an explicit factor.

**Tech Stack:** Agda `--safe`, Haskell `runghc` generator, GitHub Actions.

**Spec:** The existing theorem-first exploration surface and current PR #27.

## Global Constraints

- Canonical mathematical authority is Agda `--safe`.
- Actual exploration methods are MR15, OpenES, and coupled Noisy Nets.
- Flat Dyadic is the only selectable probability-law module.
- Retired non-flat law modules are absent from the active theorem surface.
- The legacy triangular law is pruned and guarded against reintroduction.
- No empirical/data analysis is introduced.

---

### Task 1: Define the retained law and full theorem boundary

**Files:**
- `Exotic/ERL/Exploration/FlatDyadic.agda`
- `Exotic/ERL/Exploration/DyadicLaw.agda`
- `Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda`
- `Exotic/ERL/FullCoupled/SoftsignGatedRepresentation.agda`

- [x] Flat Dyadic is uniform over all 256 Int8 codes with exact denominator 256.
- [x] Prove normalization, zero support, ±1 support, and universal positive support.
- [x] Make `DyadicLaw` contain only `flatDyadic`.
- [x] Make `FullAlgebraicCoupling` carry normalization, unit support, canonical softsign-gated `PeriodOne`, representation forward/pullback laws, explorer irreducibility, self-loop, and derived period one.

### Task 2: Generate the endogenous frontier

**Files:**
- `.ci/discovery/ExplorationTheoremGenerator.hs`
- `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`

- [x] Enumerate MR15, OpenES, and Noisy Nets against Flat Dyadic only.
- [x] Emit exactly three `Endogenous` theorem objects through `composeFull`.
- [x] Pass exact normalization and unit-generator support into the theorem boundary.
- [x] Keep Haskell as source generation only; Agda `--safe` is the acceptance oracle.

Expected theorem names:
`MR15FlatDyadicEndogenous`, `OpenESFlatDyadicEndogenous`, `NoisyNetFlatDyadicEndogenous`.

### Task 3: Connect Noisy Nets to the representation layer

**Files:**
- `Exotic/ERL/FullCoupled/SoftsignGatedRepresentation.agda`
- `Exotic/ERL/FullCoupled/NoisyNetSoftsignFactor.agda`
- `Exotic/efficient_chad/SoftsignGatedComposition.agda`
- `Exotic/efficient_chad/MobiusSoftsignBridge.agda`

- [x] The canonical representation is `Int8 × Int8` at the softsign-gated boundary.
- [x] Prove projection/section for the Noisy-Net coupled state.
- [x] Prove every representation step lifts into the coupled Noisy-Net relation.
- [x] Prove every coupled Noisy-Net step projects to the representation relation.
- [x] Prove representation irreducibility, self-loop, and period one.
- [x] Prove full coupled Noisy-Net irreducibility and self-loop.
- [x] Exhibit distinct coupled states with the same representation projection, establishing a proper strict state extension.
- [x] Prove conditional Möbius closure of signReLU8→softsign8 from concrete activation witnesses.

### Task 4: Strict theorem ordering

- [x] Define the scalar quotient factor from MR15 to OpenES.
- [x] Define the Noisy-Net factor from the coupled state to MR15 through the explicit representation bridge.
- [x] Prove `OpenES < MR15 < NoisyNet` as a structural factor-extension chain with proper-fiber separators.
- [x] Transfer irreducibility, self-loop, and `PeriodOne` through each factor.
- [ ] Replace any remaining witness-bundle-only comparison with named semantic factor-order properties where needed by the final reviewer.

The ordering ignores probability statistics: Noisy Nets is strictly strongest only because its theorem state strictly extends the representation theorem state; MR15 strictly extends the scalar quotient; this is not a performance ranking.

### Task 5: CI acceptance

- [x] Remove obsolete law-module workflow checks for pruned variants.
- [x] Add retained Flat Dyadic, full coupling, softsign-gated composition, conditional Möbius bridge, and Noisy-Net projection checks.
- [ ] Require a fresh green run after the latest head is pushed.
