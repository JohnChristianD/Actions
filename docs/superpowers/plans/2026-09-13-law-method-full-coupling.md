# Law-Method Full-Coupling Theorem Permutations Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the exploration theorem generator emit only endogenous theorem artifacts for every actual explorer × dyadic probability-law permutation after the full algebraic coupling composition, with the legacy triangular law permanently pruned from the selectable law universe.

**Architecture:** `DyadicLaw` is a finite law tag plus exact normalization/support facts. Actual explorer modules remain MR15, OpenES, and coupled Noisy Nets. `FullAlgebraicCoupling` is the theorem boundary that composes one actual explorer with one law and derives PeriodOne only from the composed proof object. The Haskell generator enumerates method × law permutations and emits only those composed theorem objects; Agda `--safe` remains the acceptance authority.

**Tech Stack:** Agda `--safe`, Haskell `runghc` generator, GitHub Actions.

**Spec:** The existing theorem-first exploration surface and current PR #27.

## Global Constraints

- Canonical mathematical authority is Agda `--safe`.
- Actual exploration methods are MR15, OpenES, and coupled Noisy Nets.
- Lazy Walk and Dyadic Ladder are probability-law modules, not exploration methods.
- The selectable law universe contains Lazy Walk and Dyadic Ladder only.
- The legacy triangular law is not selectable and is guarded against reintroduction by the permanent theorem-scope checker.
- No empirical/data analysis is introduced.

---

### Task 1: Define the dyadic-law composition surface

**Files:**
- Create: `Exotic/ERL/Exploration/DyadicLaw.agda`
- Create: `Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda`

**Interfaces:**
- `DyadicLaw` exports `lazyWalk` and `dyadicLadder`.
- `law-normalized` maps each law tag to its checked exact normalization proof.
- `law-unit-support` maps each law tag to its checked positive unit-step support facts.
- `FullAlgebraicCoupling law step` stores the law normalization theorem, explorer irreducibility theorem, explorer self-loop theorem, and derived period-one theorem.
- `composeFull` constructs the composition from these proof components.

- [ ] **Step 1: Add the law tag and exact proof interface.**

```agda
data DyadicLaw : Set where
  lazyWalk : DyadicLaw
  dyadicLadder : DyadicLaw
```

Each case delegates to the already checked exact law module and exposes only finite dyadic normalization/support facts.

- [ ] **Step 2: Add the full algebraic coupling theorem record.**

```agda
record FullAlgebraicCoupling {S : Set}
    (law : DyadicLaw) (_—→_ : S → S → Set) : Set where
  constructor fullAlgebraicCoupling
  field
    lawNormalized : law-normalized law
    irreducible : Irreducible _—→_
    selfLoop : SelfLoop _—→_
    periodOne : PeriodOne _—→_
```

- [ ] **Step 3: Make `composeFull` derive `periodOne` through the existing schema theorem.**

```agda
composeFull : ∀ {S : Set} (law : DyadicLaw) {_—→_ : S → S → Set}
  → law-normalized law
  → Irreducible _—→_
  → SelfLoop _—→_
  → FullAlgebraicCoupling law _—→_
composeFull law normalized r loop = fullAlgebraicCoupling
  normalized r loop (periodOne-from-components r loop)
```

- [ ] **Step 4: Check both new modules with `agda --safe`.**

Run: `agda --safe Exotic/ERL/Exploration/DyadicLaw.agda` and `agda --safe Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda`
Expected: PASS.

- [ ] **Step 5: Commit.**

```bash
git add Exotic/ERL/Exploration/DyadicLaw.agda Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda
git commit -m "feat: add law-aware full coupling theorem surface"
```

### Task 2: Generate every law × method permutation

**Files:**
- Modify: `.ci/discovery/ExplorationTheoremGenerator.hs`
- Modify: `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`

**Interfaces:**
- `Method` continues to describe MR15, OpenES, and Noisy Nets.
- `Law` describes Lazy Walk and Dyadic Ladder plus the law normalization proof name.
- `renderPermutation` emits an `Endogenous` theorem value only through `composeFull`.

- [ ] **Step 1: Add the two-law metadata table.**

```haskell
data Law = Law
  { lawName :: String
  , lawCtor :: String
  , normalizationName :: String
  }

laws :: [Law]
laws =
  [ Law "LazyWalk" "lazyWalk" "lazyWalkNormalized"
  , Law "DyadicLadder" "dyadicLadder" "dyadicLadderNormalized"
  ]
```

- [ ] **Step 2: Replace method-only rendering with a method × law product.**

For every `Method m` and `Law l`, emit:

```agda
MR15LazyWalkEndogenous : FullAlgebraicCoupling lazyWalk MR15Step
MR15LazyWalkEndogenous = composeFull lazyWalk lazyWalkNormalized
  mr15IrreducibilityProof mr15SelfLoopProof
```

and the corresponding OpenES and NoisyNet values, with no standalone law theorem output.

- [ ] **Step 3: Import the law and full-coupling modules into the generated harness.**

- [ ] **Step 4: Run the generator and then `agda --safe` on its generated output.**

Run: `runghc .ci/discovery/ExplorationTheoremGenerator.hs`
Expected: generator exits zero and writes six law × method theorem values.

Run: `agda --safe Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`
Expected: PASS.

- [ ] **Step 5: Commit.**

```bash
git add .ci/discovery/ExplorationTheoremGenerator.hs Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda
git commit -m "feat: generate endogenous law-method theorem permutations"
```

### Task 3: Permanently prune the legacy triangular law

**Files:**
- Modify: `.ci/check-forbidden-theorems.py`

**Interfaces:**
- Existing finite/dyadic theorem-scope guard gains encoded tokens for the legacy law name and compact spelling, preventing accidental reintroduction without exposing the guard's own vocabulary.

- [ ] **Step 1: Add encoded forbidden tokens for the legacy law identifiers.**

- [ ] **Step 2: Run the scope guard.**

Run: `python3 .ci/check-forbidden-theorems.py`
Expected: `finite-dyadic-theorem-scope=clean`.

- [ ] **Step 3: Commit.**

```bash
git add .ci/check-forbidden-theorems.py
git commit -m "chore: permanently prune legacy triangular law"
```

### Task 4: Verify the full canonical gate

**Files:**
- Check: `.github/workflows/agda.yml`

**Interfaces:**
- Existing workflow continues to validate canonical Agda, individual explorers, law modules, generated theorem harness, and theorem-scope guard.

- [ ] **Step 1: Run all directly available local checks.**

Run:
```bash
python3 .ci/check-forbidden-theorems.py
agda --safe Exotic/ERL/Exploration/DyadicLaw.agda
agda --safe Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda
runghc .ci/discovery/ExplorationTheoremGenerator.hs
agda --safe Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda
```

- [ ] **Step 2: Inspect the generated source for exactly six composed theorem values.**

Expected pairs:
`MR15 × LazyWalk`, `MR15 × DyadicLadder`, `OpenES × LazyWalk`, `OpenES × DyadicLadder`, `NoisyNet × LazyWalk`, `NoisyNet × DyadicLadder`.

- [ ] **Step 3: Commit the final verification output if source changes are needed.**

```bash
git status --short
git diff --check
```
