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

## 2026-09-24 GRU-F4 economic injectivity follow-up

- Added the first concrete injectivity composition seam after auditing the existing GRU/F4 global observation theorem and Mega Walrasian global square.
- Added gruf4EconomicInjectivityFromGlobalSquare to the canonical Agda monolith. It returns the existing learner-side F4/NormPair/GRU injectivity witness together with the economic encode injectivity derived from the exact global square.
- Added CI discovery/gate coverage for that theorem symbol.
- Updated the economic graph and narrative to show injectivity as supporting evidence, while retaining convergence and fixed-point-to-equilibrium as explicit frontier obligations.
- Knowledge delta paths: TheoremsMonolith.agda, .ci/actions_ci.dhall, .ci/discovery/theorem_graph_search.m, docs/economics/economic-egraph-emergent-arrow-debreu.mmd, docs/economics/economic-egraph-emergent-arrow-debreu.md, this plan.
- Verification limitation: no Agda compiler is installed in the execution environment; repository CI has not yet been observed running for the new head.


## 2026-09-24 finite-rank convergence bridge follow-up

- Added `topologicalConvergenceWitness-from-finite-rank-stability` to compose the existing `FiniteRankStabilityCertificate` eventual-exact fixation with the existing `TopologicalConvergenceWitness` interface.
- Kept the convergence relation explicit as a premise, including eventual-equilibrium convergence and equality transport. The theorem therefore does not claim that finite-rank descent alone proves a topological convergence theorem.
- Added CI gate and theorem-discovery coverage for the new bridge.
- Updated the economic graph/docs to expose finite-rank stability as a conditional convergence bridge.
- Knowledge delta paths: `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`, `.ci/actions_ci.dhall`, `.ci/discovery/theorem_graph_search.m`, `docs/economics/economic-egraph-emergent-arrow-debreu.mmd`, `docs/economics/economic-egraph-emergent-arrow-debreu.md`, this plan.
- Verification limitation: Agda is not installed locally; the new theorem requires CI typechecking before it can be treated as verified.


## 2026-09-24 finite-rank bridge correction follow-up

- Audited the new `topologicalConvergenceWitness-from-finite-rank-stability` bridge before treating it as verified.
- Found and corrected the equality orientation in the eventual-equilibrium convergence application: the orbit witness and eventual fixation compose as `trans (orbitMatches n) orbitFixed`.
- This is a proof-term correction only; the convergence relation and equality-transport premises remain explicit.
- Verification limitation: Agda is not installed locally; the corrected head requires CI typechecking.


## 2026-09-24 finite-rank bridge CI verification

- Workflow `Nix connected composition verification` run #1193 completed successfully for head `d8fc834d8619a0df2b40bbf08aefb7fd5017dd15`.
- The corrected `topologicalConvergenceWitness-from-finite-rank-stability` proof term is therefore accepted by the repository's CI typechecking/composition gate.
- The next closure seam was audited against the existing theorem surface. `CanonicalF4GlobalOptimizerStabilityTheorem` supplies exact F4 step-stability facts, but no existing theorem supplies the required `FiniteRankStabilityCertificate.eventualExact` field for the composed MARL/Hodge-Maxwell/GRU-F4/Watkins/Sparsemax economic update.
- No artificial F4-to-eventual-fixation theorem was added. The remaining obligation is the actual finite-rank/eventual-absorption certificate for the composed update.
