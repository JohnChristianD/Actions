# Sign-q-IDBD CI Migration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace legacy Python/Ruby repair CI with Elixir+Agda, make sign-q-IDBD canonical, add the composed-sign finite theorem stack, preserve the Pareto mapping certificate, and land the branch only after fresh green verification.

**Architecture:** `Exotic/ERL/FullCoupled/SignQIDBDComposed_v153.agda` is the new small canonical theorem surface. `CompleteSafe_v147.agda` remains a compatibility target only and is repaired directly so the kernel, not a mutator, validates it. CI uses one deterministic Elixir normaliser and Agda `--safe` checks; historical repair workflows and Python/Ruby files are deleted.

**Tech Stack:** Agda 2.8.0 `--safe`, Elixir `.exs`, GitHub Actions, exact Haskell/Elixir/Rational oracle checks where already present.

**Spec:** `docs/superpowers/specs/2026-09-10-sign-qidbd-ci-migration-design.md`

## Global Constraints

- Default learner update is sign-q-IDBD: `meta -> raw direction -> q-projection -> parameter-direction sign -> coupled dyadic L2 -> weights`.
- Do not sign beta, traces, or IDBD meta-state.
- Keep LayerNorm and unnormalised LSTM out of the canonical theorem.
- Use fixed-window finite hard attention and finite positional tables; do not introduce softmax, exp/log attention, or analytic mean-value/Taylor claims.
- Retain the finite Pareto-efficient coupled hyperparameter mapping as a certificate only.
- Optional per-feature momentum may exist only between q-projection and parameter-direction sign.
- No gradient averaging.
- No Python or Ruby CI/repair scripts after migration.
- Agda `--safe` is the semantic authority; no unsafe postulates or unsolved metas.
- No data analysis is performed.
- Squash merge only after fresh green verification; finish with zero open pull requests in the repository.

---

### Task 1: Canonical sign-q-IDBD composed theorem

**Files:**
- Create: `Exotic/ERL/FullCoupled/SignQIDBDComposed_v153.agda`
- Test: `.github/workflows/agda.yml`

**Interfaces:**
- Consumes: Agda builtins only.
- Produces: `signQIDBDUpdate`, `featureMomentumUpdate`, `hardAttention`, `onePathNorm`, `dyadicL2`, `ParetoMapping`, `doubleSignCompose`, `eventualSignStability`, and `canonicalComposition`.

- [ ] **Step 1: Add a self-contained `--safe` module.**

```agda
{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SignQIDBDComposed_v153 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

Bool : Set
Bool = Set
```

Replace the illustrative Bool fragment with actual self-contained finite definitions before committing. The final file must define finite sign, vectors, finite sums, branch records, and all theorem fields without external libraries.

- [ ] **Step 2: Encode sign-q-IDBD with optional feature momentum.**

Required semantic equations:

```text
raw = idbdDirection(meta, trace, gradient)
qraw = qProject(raw)
m' = mu * m + qraw
parameterDirection = sign(m' - l2Direction(theta))
theta' = theta + step * parameterDirection
```

The non-momentum default is represented by `mu = 0`, so the canonical branch remains sign-q-IDBD.

- [ ] **Step 3: Encode the finite invariants.**

Use a finite absolute-weight path norm, dyadic block penalties `2^-k`, finite-width hard attention with deterministic argmax/tie choice, finite Pareto maximality, and two sequential sign branches.

- [ ] **Step 4: Add the sign-switching certificate.**

State only the finite implication:

```text
eventual sign separation -> finite absence of later directional switches
```

Do not assert universal no-chattering from convergence.

- [ ] **Step 5: Add the composed closure theorem.**

The exported theorem packages the invariants for transformer -> representation -> sign-q-IDBD -> dyadic-L2 -> Pareto mapping -> second sign branch.

- [ ] **Step 6: Commit and wait for the authoritative Agda run.**

Commit message:

```text
feat: make sign-q-IDBD canonical composed theorem
```

---

### Task 2: Repair the compatibility monolith at the actual kernel root

**Files:**
- Modify: `Exotic/ERL/FullCoupled/CompleteSafe_v147.agda`

**Interfaces:**
- Consumes: existing monolith declarations.
- Produces: a directly kernel-checkable compatibility surface with no nonexistent `OrderedRing.base` projection.

- [ ] **Step 1: Replace the failed projection.**

At the `SmoothAlgebra` boundary replace:

```agda
Ring._*_ (OrderedRing.base orderedRing) ...
```

with:

```agda
Ring._*_ (OrderedRing.ring orderedRing) ...
```

and similarly replace the scalar alias:

```agda
Scalar S = Ring.R (OrderedRing.ring (SmoothAlgebra.orderedRing S))
```

- [ ] **Step 2: Remove imports that refer to non-exported Equality names.**

Use only exported builtins required by the current source, e.g. `_≡_` and `refl`; define local helper lemmas where needed.

- [ ] **Step 3: Run the authoritative `agda --safe` check.**

Use the exact command from CI:

```text
agda --safe Exotic/ERL/FullCoupled/CompleteSafe_v147.agda
```

- [ ] **Step 4: For each new failure, investigate the exact kernel error and patch only one root cause at a time.**

Do not add a bulk source rewriter to hide errors.

- [ ] **Step 5: Commit each independently green root-cause repair.**

---

### Task 3: Replace Python/Ruby repair infrastructure with Elixir + Agda

**Files:**
- Create: `.ci/normalise_agda.exs`
- Create: `.ci/NormaliseAgda.agda`
- Modify: `.github/workflows/agda.yml`
- Delete: all repository `.ci/*.py` repair/normalisation helpers
- Delete: all repository `.ci/*.rb` repair/normalisation helpers
- Delete: workflows whose only purpose is parser/normalisation mutation

**Interfaces:**
- `normalise_agda.exs` reads the canonical file, applies only named idempotent namespace repairs, and exits nonzero on ambiguous matches.
- `NormaliseAgda.agda` checks the finite invariants and source-level normalisation contract under `--safe`.

- [ ] **Step 1: Create the Elixir normaliser.**

It must:

```text
read -> exact textual match -> replace once -> verify postcondition -> write only when changed
```

It must never invoke Python or Ruby and must not contain heuristic global rewrites.

- [ ] **Step 2: Create the Agda normalisation certificate.**

It certifies the named namespace identities and finite theorem surface, while leaving semantic proof to the individual Agda modules.

- [ ] **Step 3: Simplify `agda.yml`.**

Use Agda 2.8.0, install Elixir, run the single normaliser, then run all canonical Agda checks. Remove Ruby/Python installation and execution from the workflow.

- [ ] **Step 4: Delete obsolete repair workflows.**

Remove `force-v149-monolith-repair.yml`, `repair-monolith-parser.yml`, `repair-v149-dedupe.yml`, and any other workflow whose primary function is historical parser mutation. Retain only authoritative theorem/oracle workflows.

- [ ] **Step 5: Delete the standalone Ruby/Python oracle files from CI if referenced by the workflows.**

Retain exact Haskell/Elixir oracles where they serve current cross-checks.

- [ ] **Step 6: Commit.**

```text
ci: replace Python and Ruby repair machinery with Elixir Agda
```

---

### Task 4: Remove obsolete sign/LayerNorm legacy surfaces from the canonical gate

**Files:**
- Modify: `.github/workflows/agda.yml`
- Modify: `docs/EFFICIENT_CHAD_V150_TARGET.md`
- Modify: `docs/EMERGENT_AGDA_THEOREM_CATALOG.md`

- [ ] **Step 1: Remove `RepresentationLayerNormClosure.agda` from required canonical checks.**

- [ ] **Step 2: Make `SignQIDBDComposed_v153.agda` the first-class theorem target.

- [ ] **Step 3: Describe `CompleteSafe_v147.agda` explicitly as compatibility/kernel surface, not as the semantic source for new claims.

- [ ] **Step 4: Record sign-q-IDBD as the default update mode and momentum as optional.

- [ ] **Step 5: Record the retained Pareto mapping as a finite certificate, not empirical optimisation evidence.

- [ ] **Step 6: Commit.**

```text
docs: promote modular sign-q-IDBD theorem surface
```

---

### Task 5: Add conjecture-generation and finite interpolation gates

**Files:**
- Modify: `Exotic/ERL/FullCoupled/CIInterpolation_v147.agda`
- Create: `Exotic/ERL/FullCoupled/ConjectureGeneration_v153.agda`
- Modify: `.github/workflows/agda.yml`

- [ ] **Step 1: Keep interpolation finite and algebraic.**

Use finite branch interpolation records and explicit witnesses rather than Taylor-series or analytic remainder semantics.

- [ ] **Step 2: Add conjecture candidates as data.**

A conjecture record must carry a finite statement, dependencies, and a status indicating unproved/certified. Only an Agda proof term promotes a candidate to theorem status.

- [ ] **Step 3: Add the composed theorem candidate for double-sign switching.**

- [ ] **Step 4: Add the composed theorem candidate for optional feature momentum.

- [ ] **Step 5: Kernel-check both modules.

- [ ] **Step 6: Commit.

```text
feat: add finite interpolation and conjecture gate
```

---

### Task 6: CI iteration and root-cause repair loop

**Files:**
- Modify only files named by fresh CI failures.

- [ ] **Step 1: Push/advance the PR head by a verified commit.

- [ ] **Step 2: Read every failing workflow job and exact compiler error before editing.

- [ ] **Step 3: Apply one root-cause change.

- [ ] **Step 4: Re-run failed jobs only when the failure is isolated; otherwise trigger a fresh authoritative run.

- [ ] **Step 5: Check the complete safe matrix after each structural change.

- [ ] **Step 6: Continue until all required checks are green.

---

### Task 7: Final hygiene, PR closure, and squash merge

**Files:**
- None unless hygiene checks identify a remaining file.

- [ ] **Step 1: Verify repository tree contains no Python repair/CI files and no Ruby repair/CI files.

- [ ] **Step 2: Verify no workflow executes `python`, `python3`, `ruby`, or `.rb` repair scripts.

- [ ] **Step 3: Verify fresh green Agda 2.8.0 `--safe` checks and current exact oracles.

- [ ] **Step 4: Verify the Pareto mapping, sign-q-IDBD default, optional momentum, fixed-window hard-attention, dyadic-L2, and double-sign theorem are all present in the canonical surface.

- [ ] **Step 5: Mark PR #21 ready only if its state requires it, then squash-merge into `main` using the expected head SHA.

- [ ] **Step 6: Verify PR #21 is merged and `search_prs` reports zero open PRs in `JohnChristianD/Actions`.

- [ ] **Step 7: Verify `main` has fresh green required checks after the squash merge.
