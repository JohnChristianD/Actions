# Nix-backed CI Migration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove the retired non-Nix execution layer and run the Agda proof lane plus Mercury verifier/e-graph lanes from one pinned Nix environment while preserving the current theorem and discovery contracts.

**Architecture:** GitHub Actions installs Nix once, enters the repository's flake devShell, and runs lane-specific commands from a small POSIX shell driver. Mercury comes from Nixpkgs. Agda 2.8.0.2 and standard-library 2.4 come from the official Agda setup action.

**Tech Stack:** GitHub Actions, Nix flakes, pinned nixpkgs, Agda 2.8.x + standard-library package set, Mercury, POSIX shell.

**Spec:** Current request: prune the retired CI layer and consolidate CI on Nix, and preserve kernel-check plus Mercury e-graph verification.

## Global Constraints

- Preserve `TheoremsMonolith.agda` as the canonical theorem source.
- Preserve `.ci/discovery/` Mercury source and executable e-graph checks.
- Keep `--safe` on the Agda proof lane.
- Do not weaken or delete theorem checks merely to obtain a green run.
- Remove all repository-controlled files from the retired CI layer.
- Keep the CI environment deterministic through a pinned flake lock.

## Review Focus

- Agda/stdlib compatibility: the selected Nix package set must expose the standard library used by the repository's imports.
- Mercury build/runtime: all current Mercury verifier and e-graph programs must compile and execute from the same Nix shell.
- Runner lifecycle: the Agda lane must no longer depend on the retired CI bootstrap or shell process boundaries.
- Surface audit: no legacy package-source or retired workflow/config remnants should remain.
- Evidence quality: CI must distinguish a kernel failure from a runner/process failure.

---

### Task 1: Add the Nix environment

**Files:**
- Create: `flake.nix`
- Create: `flake.lock` via Nix tooling in a future local/CI refresh if available.

- [x] Step 1: Define a pinned nixpkgs input and a default devShell containing Mercury, GNU make, and git.
- [x] Step 2: Use the official Agda setup action for Agda 2.8.0.2 and standard-library 2.4.
- [x] Step 3: Keep Mercury sourced from nixpkgs.
- [x] Step 4: Avoid the retired non-Nix execution layer entirely.

### Task 2: Replace the retired CI driver

**Files:**
- Create: `.ci/ci.sh`
- Delete: the retired CI driver, manifest, and channel files

- [x] Step 1: Port the existing lane dispatch into POSIX shell without changing the lane contracts.
- [x] Step 2: Keep the Agda file list and `--safe` invocations unchanged.
- [x] Step 3: Keep Mercury forbidden-theorem and e-graph commands unchanged.
- [x] Step 4: Keep the canonical single-theorem-source and forbidden-surface audits.

### Task 3: Replace GitHub Actions environment

**Files:**
- Replace the retired GitHub workflow with the Nix-backed workflow.

- [x] Step 1: Install Nix with a pinned action.
- [x] Step 2: Run all four lanes from the same flake devShell.
- [x] Step 3: Use the NixOS-maintained nix-installer action and the official Agda setup action with pinned versions.
- [x] Step 4: Keep all verification lanes in one Nix shell invocation.
- [x] Step 5: Emit tool versions before lane execution.

### Task 4: Update repository documentation

**Files:**
- Modify: `README.md`
- Modify: `.ci/change-record-2026-09-19-uap-agda-2.8.0.2.json`

- [x] Step 1: Replace retired bootstrap documentation with Nix environment documentation.
- [x] Step 2: Record that Mercury is supplied through Nixpkgs.
- [x] Step 3: Record the CI diagnosis as a runner/process-boundary investigation, not a theorem rejection.
- [x] Step 4: Keep the bounded exact-UAP theorem statement and its proof dependencies intact.

### Task 5: Verify

- [x] Step 1: Create a pull request from `nix-prune-mercury-ci` into `main` (blocked by the GitHub integration with HTTP 403; branch remains available).
- [ ] Step 2: Observe the new CI run.
- [ ] Step 3: If Nix evaluation or package compatibility fails, fix only the environment wiring and re-run; do not weaken theorem gates.
- [ ] Step 4: Confirm Agda kernel checks and Mercury e-graph checks execute rather than being skipped.


## Follow-up: finite precision, Nat coding, and theorem/e-graph synchronization

### Goal

Make the finite/discrete exact-UAP boundary explicit without importing reservoir terminology into the RL model, and make Mercury's equality-saturation layer consume only the theorem surface proven by the canonical Agda monolith.

### Architecture

`CanonicalLearnerMonolith.agda` owns the minimal topology, discrete topology witness, finite `Int8` algebra, and learner/RL definitions. `TheoremsMonolith.agda` owns the exact-UAP factorization, infinite `Nat` orbit embedding, finite-`Int8` contradiction, and proof-source theorem contracts. Mercury consumes the source-derived theorem manifest and verifies the named dependencies with equality saturation; Agda `--safe` remains the proof authority.

### Knowledge delta

- `README.md`: distinguish this learned 2-RNN/SSRN/finite-automata/Moore-style RL algebra from reservoir computing; explain the exact Nat-vs-Int8 cardinality boundary and the topology/import result.
- `.ci/change-record-2026-09-19-uap-agda-2.8.0.2.json`: record the new theorem and Mercury synchronization contracts.
- `.ci/discovery/theorem_monolith_egraph_sync.m`: require the exact UAP, topology boundary, Nat-orbit, and finite-Int8 contradiction declarations.
- `.ci/discovery/interpolated_theorem_egraph.m`: include the same theorem dependencies in the semantic e-graph target.
- `.ci/discovery/interpolated_theorem_egraph_test.m`: exercise the synchronization gate.
- `.ci/discovery/symbolic_egraph_test.m`: exercise e-matching, saturation, rebuild, analysis, and extraction.
- `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`: add only theorem contracts justified by the existing finite/discrete algebra.

### Review focus

1. Do not claim that finite-dimensional reservoir universality requires infinite width; the 2024 reservoir result supplies a finite-output counterexample.
2. Do not claim neighborhood separation is inherently equivalent to infinite precision or infinite data in arbitrary topology; the repo proves only the finite-codomain exact-left-inverse obstruction.
3. Do not claim `Nat` codomain alone is sufficient for exact universality; require an explicit left inverse/injectivity composition on the relevant orbit.
4. Do not reintroduce ordered-semiring or sorting dependencies absent from the existing proof import surface.
5. Do not let Mercury outrank Agda proof authority or fabricate theorem dependencies not extracted from the monolith.

### Verification

The single CI shell must run Agda `--safe`, Mercury theorem checks, source-derived e-graph synchronization, equality-saturation regression tests, and the repository surface audit from the same pinned Nix environment.


## Follow-up: theorem-only equality saturation and canonical mix-prefix composition

Restrict semantic extraction to `TheoremsMonolith.agda`; the learner monolith remains imported canonical semantics but is never e-graphed. Compose existing Hadamard orthogonality, attention mixing, Walsh-Rademacher phase periodicity, endogenous attention mediation, associative prefix scan, target-prefix correctness, and exact prefix work/count laws into `CanonicalHadamardAttentionRopePrefixCompositionTheorem`. Prune environment-dependent Sion/regret/sample-complexity claims. Do not import CHAD merely for complexity vocabulary: it is a separate reverse-AD transformation semantics.


## Theorem-only e-graph scope

- Mercury semantic extraction source is exactly `TheoremsMonolith.agda`.
- `CanonicalLearnerMonolith.agda` remains an imported Agda proof dependency and kernel-check target, but its declarations are not e-graph nodes.
- The canonical forced theorem exposes `CanonicalHadamardAttentionRopePrefixCompositionTheorem` as a first-class field so the e-graph derives the Hadamard/attention/RoPE/associative-prefix/work composition from theorem declarations.
- Do not add Sion or environment-dependent sample-complexity/regret theorems without an explicit stochastic environment contract.


## Follow-up: injectivity and finite library boundary

- Treat finite-capacity impossibility as `Nat → Fin bound`, not as impossibility of embedding Nat into arbitrary infinite rings.
- Name the state-orbit wrapper as orbit injectivity rather than ring injectivity; no ring structure is implied by that theorem.
- Do not import full `Fin` or `Vec` libraries merely for Mercury search convenience. Add only theorem-relevant modules and properties.
- Keep Mercury semantic extraction restricted to `TheoremsMonolith.agda`; imported learner definitions remain Agda-only proof dependencies.


## Follow-up: emergent finite-exact orbit/UAP target

- Use `CanonicalFiniteExactOrbitUAPCompositionTheorem` as the Mercury forced target.
- Compose theorem certificates only; `CanonicalLearnerMonolith.agda` remains the sole component semantic source.
- Keep exact continuous/bounded/recurrent UAP, left-inverse injectivity, finite-code contradiction, finite-time/sample readout, exact iterate composition, aperiodicity, finite-cycle exclusion, and finite state/action visit capacity.
- Prune generic convexity/concavity, Sion, regret, and sample-complexity abstractions when their concrete canonical witnesses are absent.
- Do not introduce compression=prediction or Turing-completeness claims without a concrete formal statement and proof.
