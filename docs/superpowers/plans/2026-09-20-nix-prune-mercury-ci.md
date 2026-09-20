# Nix-backed CI Migration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove the Guix/Scheme execution layer and run the Agda proof lane plus Mercury verifier/e-graph lanes from one pinned Nix environment while preserving the current theorem and discovery contracts.

**Architecture:** GitHub Actions installs Nix once, enters the repository's flake devShell, and runs lane-specific commands from a small POSIX shell driver. Mercury comes from Nixpkgs. Agda 2.8.0.2 and standard-library 2.4 come from the official Agda setup action.

**Tech Stack:** GitHub Actions, Nix flakes, pinned nixpkgs, Agda 2.8.x + standard-library package set, Mercury, POSIX shell.

**Spec:** Current request: prune Guix/Scheme, consolidate CI on Nix, and preserve kernel-check plus Mercury e-graph verification.

## Global Constraints

- Preserve `TheoremsMonolith.agda` as the canonical theorem source.
- Preserve `.ci/discovery/` Mercury source and executable e-graph checks.
- Keep `--safe` on the Agda proof lane.
- Do not weaken or delete theorem checks merely to obtain a green run.
- Remove all repository-controlled Guix and Guile CI files.
- Keep the CI environment deterministic through a pinned flake lock.

## Review Focus

- Agda/stdlib compatibility: the selected Nix package set must expose the standard library used by the repository's imports.
- Mercury build/runtime: all current Mercury verifier and e-graph programs must compile and execute from the same Nix shell.
- Runner lifecycle: the Agda lane must no longer depend on Guix bootstrap or Guix shell process boundaries.
- Surface audit: no `.scm` or Guix workflow/config remnants should remain.
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

### Task 2: Replace Scheme CI driver

**Files:**
- Create: `.ci/ci.sh`
- Delete: `.guix/ci.scm`
- Delete: `.guix/manifest.scm`
- Delete: `.guix/channels.scm`

- [x] Step 1: Port the existing lane dispatch into POSIX shell without changing the lane contracts.
- [x] Step 2: Keep the Agda file list and `--safe` invocations unchanged.
- [x] Step 3: Keep Mercury forbidden-theorem and e-graph commands unchanged.
- [x] Step 4: Keep the canonical single-theorem-source and forbidden-surface audits.

### Task 3: Replace GitHub Actions environment

**Files:**
- Modify: `.github/workflows/guix-composition.yml` (rename is optional; contents must become Nix-backed CI).

- [x] Step 1: Install Nix with a pinned action.
- [x] Step 2: Run all four lanes from the same flake devShell.
- [x] Step 3: Use the NixOS-maintained nix-installer action and the official Agda setup action with pinned versions.
- [x] Step 4: Keep all verification lanes in one Nix shell invocation.
- [x] Step 5: Emit tool versions before lane execution.

### Task 4: Update repository documentation

**Files:**
- Modify: `README.md`
- Modify: `.ci/change-record-2026-09-19-uap-agda-2.8.0.2.json`

- [x] Step 1: Replace Guix bootstrap documentation with Nix environment documentation.
- [x] Step 2: Record that Mercury is supplied through Nixpkgs.
- [x] Step 3: Record the CI diagnosis as a runner/process-boundary investigation, not a theorem rejection.
- [x] Step 4: Keep the bounded exact-UAP theorem statement and its proof dependencies intact.

### Task 5: Verify

- [x] Step 1: Create a pull request from `nix-prune-mercury-ci` into `main` (blocked by the GitHub integration with HTTP 403; branch remains available).
- [ ] Step 2: Observe the new CI run.
- [ ] Step 3: If Nix evaluation or package compatibility fails, fix only the environment wiring and re-run; do not weaken theorem gates.
- [ ] Step 4: Confirm Agda kernel checks and Mercury e-graph checks execute rather than being skipped.
