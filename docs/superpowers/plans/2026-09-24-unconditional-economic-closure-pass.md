# Unconditional Economic Closure Pass Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the unattended economic graph distinguish and verify the complete unconditional target path without promoting unsupported mathematical implications to proved status.

**Architecture:** Preserve Agda as proof authority. Add explicit nodes for the two remaining upstream closure seams: deriving convergence/fixed-point existence from economic assumptions, and deriving the fixed-point-to-equilibrium bridge. Keep the existing conditional theorem intact and make CI fail if the unconditional graph is labeled closed without concrete proof artifacts. Cross-language Econlib existence remains an external evidence source until an explicit adapter is present.

**Tech Stack:** Agda, Dhall/Nix CI, Mercury discovery, Mermaid/Markdown.

**Spec:** `docs/economics/economic-egraph-emergent-arrow-debreu.md`

## Global Constraints

- Do not encode a conditional premise as an unconditional theorem.
- Agda remains the proof authority for local theorem claims.
- Mercury JSON/TSV/Mermaid are discovery/evidence views, not proof substitutes.
- Do not weaken existing CI checks.
- Keep classical Brouwer/Kakutani and convex/separation routes separate until their premises are formally connected.

## Review Focus

- Missing convergence derivation must remain visible as a blocker.
- Fixed-point-to-equilibrium must not be silently treated as a primitive.
- External Econlib existence must remain an external source until an adapter is proven.
- The graph must have one canonical status vocabulary.
- CI must reject an unconditional-closed claim when either upstream seam is absent.

---

### Task 1: Make the unconditional target explicit in the canonical graph

**Files:**
- Modify: `docs/economics/economic-egraph-emergent-arrow-debreu.mmd`
- Modify: `docs/economics/economic-egraph-emergent-arrow-debreu.md`

- [ ] Add the end-to-end target chain from economic primitives through convergence, fixed point, equilibrium, and existence.
- [ ] Mark the two missing derivations as `FRONTIER` rather than `PROVED`.
- [ ] Keep the existing conditional topological route marked `CONDITIONAL`.
- [ ] Document the exact promotion criteria for each frontier edge.

### Task 2: Add deterministic CI gates for unconditional promotion

**Files:**
- Modify: `.ci/actions_ci.dhall`
- Modify: `.ci/discovery/theorem_graph_search.m`

- [ ] Require the canonical graph to contain both frontier edges and their explicit status.
- [ ] Require the unconditional target label to remain blocked unless corresponding Agda proof symbols exist.
- [ ] Preserve existing conditional-route gates.
- [ ] Emit machine-readable status distinguishing `conditional-closed` from `unconditional-closed`.

### Task 3: Verify

**Files:**
- No source changes.

- [ ] Run the repository's available CI checks or equivalent static gates once.
- [ ] Verify the graph and CI remain synchronized.
- [ ] Verify no unconditional theorem was fabricated.
- [ ] Record any hard gate preventing mathematical closure.

### Definition of Done

The repository contains a single unattended graph that is complete as a dependency graph, explicitly marks the exact missing proof seams, and cannot report the unconditional route as closed until those proof artifacts exist.
