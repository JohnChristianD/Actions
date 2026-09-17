# Hybrid Proof Search Language Prune Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the Python/MCTX/evosax proof-search harness with a dependency-light Haskell hybrid search, prune RandomSearch and every repository Python file, and restore benchmark reference returns without restoring regret.

**Architecture:** The kernel oracle remains Agda `--safe`. The discovery layer becomes a pure Haskell hybrid consisting of MCTS-style sequential search, MR15-GA-style population mutation, and bounded A* fallback over the existing typed theorem-surface grammar. Haskell owns orchestration and emits the same generated-candidate evidence; the GitHub workflow provisions only the Agda/Haskell toolchain already used by the repository and contains no Python package setup.

**Tech Stack:** Agda 2.8.0, stdlib 2.4, Haskell `runghc`, GitHub Actions YAML, Agda theorem monoliths, stdlib `Data.List.Sort`.

**Spec:** User request on 2026-09-17: prune evosax Random Search, retain the hybrid search, remove Python/bash harness/code, restore `referenceReturn` but not regret, and retain the existing algebraic/theorem surfaces.

## Global Constraints

- No Python files remain anywhere in the repository.
- No shell script files are introduced; YAML may still invoke runner commands.
- No regret fields are restored.
- `referenceReturn` is present in `BenchEnv` and populated for all active environments.
- The proof-search acceptance oracle is always `agda --safe`.
- RandomSearch is not part of the search stack.
- No pull request; commits land directly on `main`.

---

### Task 1: Replace the Python proof-search harness with Haskell

**Files:**
- Create: `.ci/discovery/ProofSearch.hs`
- Delete: `.ci/discovery/ProofSearch.py`

**Interfaces:**
- `data Goal = Goal { goalName :: String, goalStatement :: String, proofMacros :: [(String,String)] }`
- `mctsSearch :: Goal -> Int -> IO (Maybe Candidate)`
- `mr15gaSearch :: Goal -> Int -> IO (Maybe Candidate)`
- `aStarSearch :: Goal -> Int -> IO (Maybe Candidate)`
- `searchGoal :: Goal -> Int -> String -> IO (Maybe Candidate)`
- `verifySurfaces :: IO ()`
- `main :: IO ()`

- [ ] **Step 1: Keep the three existing theorem goals and their kernel-checkable proof macros.**

```haskell
data Goal = Goal
  { goalName :: String
  , goalStatement :: String
  , proofMacros :: [(String, String)]
  }
```

- [ ] **Step 2: Implement the kernel oracle with `System.Process` and a temporary generated Agda module.**

```haskell
agdaOK :: FilePath -> IO Bool
agdaOK path = do
  (code, _, _) <- readProcessWithExitCode "agda" ["--safe", path] ""
  pure (code == ExitSuccess)
```

- [ ] **Step 3: Implement MCTS-style tree search over the finite proof grammar, using UCT-style child selection and deterministic tie-breaking.**

```haskell
mctsSearch :: Goal -> Int -> IO (Maybe Candidate)
mctsSearch goal budget = ...
```

The search must re-check every proposed candidate with the Agda oracle before returning it. No numeric reward is treated as proof.

- [ ] **Step 4: Implement MR15-GA-style population mutation without `evosax` and without RandomSearch.**

```haskell
mr15gaSearch :: Goal -> Int -> IO (Maybe Candidate)
mr15gaSearch goal populationBudget = ...
```

Use elitist selection plus multiple-point mutation over action indices, with a fixed seed and deterministic population initialization so CI is reproducible.

- [ ] **Step 5: Implement bounded A* over candidate grammar cost as the exact deterministic fallback.**

```haskell
aStarSearch :: Goal -> Int -> IO (Maybe Candidate)
aStarSearch goal budget = ...
```

- [ ] **Step 6: Run the hybrid stack in order `mcts -> mr15-ga -> astar`; never run RandomSearch.**

```haskell
searchGoal goal budget backend = do
  x <- case backend of
    "astar"   -> pure Nothing
    _         -> mctsSearch goal budget
  case x of
    Just c  -> pure (Just c)
    Nothing -> case backend of
      "mcts" -> aStarSearch goal budget
      _      -> do
        y <- mr15gaSearch goal budget
        maybe (aStarSearch goal budget) (pure . Just) y
```

- [ ] **Step 7: Emit `Exotic/ERL/Exploration/Generated/ExplorationCandidates.json` with the kernel-checked results using only `base` library functionality.**

- [ ] **Step 8: Commit the Haskell replacement.**

```text
feat: replace python theorem search with hsk hybrid proof search
```

---

### Task 2: Remove Python and Python runtime setup

**Files:**
- Delete every `*.py` file in the repository, including the 26 `.ci/*.py` scripts and `.ci/discovery/ProofSearch.py`.
- Modify: `.github/workflows/agda.yml`

**Interfaces:**
- The workflow invokes Haskell for theorem search and existing Agda checks directly.

- [ ] **Step 1: Remove the Python dependency installation step.**

```yaml
- name: Set up hybrid theorem-search runtime
  run: python -m pip install ...
```

must be absent.

- [ ] **Step 2: Replace the Python theorem-search invocation with Haskell.**

```yaml
- name: Run kernel-checked hybrid theorem search
  run: runghc .ci/discovery/ProofSearch.hs --backend auto --budget 24
```

- [ ] **Step 3: Ensure no `python`, `python3`, `pip`, or `.py` path remains in workflow YAML.**

- [ ] **Step 4: Commit the language prune.**

```text
chore: remove python automation and random search dependency
```

---

### Task 3: Restore benchmark reference returns, retain no regret

**Files:**
- Modify: `Exotic/ERL/FullCoupled/GeneralClosedLoopBenchV2.agda`

**Interfaces:**
- `BenchEnv` regains `referenceReturn : Nat`.

- [ ] **Step 1: Add the field back to `BenchEnv`.**

```agda
field actionSpace : L.ActionSpace A
      initialState : S
      referenceReturn : Nat
      stepEnv : Fin A → S → P.StepResult S
```

- [ ] **Step 2: Restore the historical finite reference values for all 12 active environments: `16`, `10`, `1`, `500`, `90`, `1`, `8`, `1`, `1`, `1`, `16`, `32` in fixture order.**

- [ ] **Step 3: Leave `LoopResult` unchanged so it still contains return/success/steps/distinctActions and no regret.**

- [ ] **Step 4: Commit the benchmark metric restoration.**

```text
fix: restore benchmark reference returns without regret
```

---

### Task 4: Verify the repository language and theorem surfaces

**Files:**
- Modify: `docs/superpowers/plans/2026-09-17-hybrid-search-language-prune.md`

- [ ] **Step 1: Check the main tree for zero `*.py` files and zero shell script files.**
- [ ] **Step 2: Re-read `.github/workflows/agda.yml` and verify no Python setup or execution remains.**
- [ ] **Step 3: Re-read the generalized benchmark and verify `referenceReturn` is present and `regret` is absent.**
- [ ] **Step 4: Re-read the theorem monolith to confirm the existing CNN bijection/quotient/equivariance, sparse-sort, and GRU-related theorem surfaces remain untouched.**
- [ ] **Step 5: Verify the main branch ref points at the final commit and report CI status honestly if a fresh green run is not available.**

