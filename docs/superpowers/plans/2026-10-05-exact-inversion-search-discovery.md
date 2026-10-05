# Exact Inversion Search Discovery Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a proof-backed bridge that combines automatic function inversion with Todd Waugh Ambridge's constructive exact-search machinery, and make Mercury discover those compositions end-to-end rather than merely checking equality/regenerating names.

**Architecture:** Keep learner semantics exclusively in `FullCoupled/CanonicalLearnerMonolith.agda`. Add the mathematical inversion/search bridge only in `FullCoupled/TheoremsMonolith.agda`, using the already-pinned TypeTopology/TWA thesis modules. Extend Mercury so its autonomous frontier searches for semantic compositions involving inversion, uniform continuity, and c-searchability; e-graph equality is a verification/quotienting mechanism, not the discovery objective.

**Tech Stack:** Agda, TypeTopology, TWA Exact Real Search modules, Haskell.Prelude/agda2hs extraction surface, Mercury semantic extractor, symbolic e-graph, A* graph search, existing inversion-plugin downstream pipeline.

**Spec:** Current conversation requirements: combine Curry/Haskell automatic inversion ideas with Exact Real Search; retain Agda proof authority; Mercury performs end-to-end autonomous discovery; learner semantics stay separate from theorem monolith.

## Global Constraints

- Do not add a new external dependency; use the already-pinned TypeTopology/TWA source tree.
- Do not move theorem claims into `CanonicalLearnerMonolith.agda`.
- Do not label e-graph equality, registry reconciliation, or code regeneration as theorem discovery.
- Automatic inversion remains a downstream computational capability; Agda proves the inversion/search contract.
- Searchability must use explicit constructive hypotheses rather than a vacuous topology witness.
- Mercury may propose and connect proof-producing paths, while Agda remains proof authority.
- Keep existing legacy aliases only where downstream compatibility requires them.

## Review Focus

- An inverse bridge must carry an actual left/right inverse proof, not a name-level “inverse” convention.
- Uniform continuity must be an explicit TWA closeness-space witness so exact search has computationally useful precision information.
- Search transport must preserve the c-searchability contract by pulling predicates back along the forward map.
- Mercury discovery must score and compose semantic capabilities, not simply rediscover syntactic equalities.
- The canonical learner monolith must remain untouched by theorem-discovery machinery.

---

### Task 1: Add the constructive inversion/search theorem bridge

**Files:**
- Modify: `FullCoupled/TheoremsMonolith.agda`

**Interfaces:**
- Add a theorem-local module parameterized by `FunExt`.
- Consume TWA `ClosenessSpace` and `csearchable`.
- Produce a generic theorem transporting c-searchability across a uniformly continuous equivalence.

- [ ] Step 1: Add a theorem-local import of the already-pinned TWA Chapter 3 search/ClosenessSpace modules.
- [ ] Step 2: Add the inverse/search certificate record with forward map, inverse map, left/right inverse laws, and uniform-continuity witnesses.
- [ ] Step 3: Define the pullback decidable uniformly-continuous predicate and prove that the c-search result transports through the inverse.
- [ ] Step 4: Expose the theorem under standard descriptive naming such as `inverse-preserves-csearchability`.
- [ ] Step 5: Add a concrete bridge theorem packaging the Haskell-inversion interpretation as a proof-backed semantic capability, without coupling the theorem to GHC internals.

### Task 2: Extend Mercury autonomous discovery

**Files:**
- Modify: `.ci/discovery/theorem_graph_search.m`
- Modify: `.ci/discovery/theorem_monolith_egraph_sync.m`
- Modify: `.ci/discovery/real_semantic_egraph.m`

**Interfaces:**
- New semantic target: the inversion/exact-search bridge theorem.
- New graph category: inversion-search capability compositions.
- e-graph remains a quotient/saturation layer.
- A* remains the path planner over theorem dependencies.

- [ ] Step 1: Add graph predicates for the inversion/search frontier.
- [ ] Step 2: Add the bridge theorem to the autonomous frontier targets.
- [ ] Step 3: Require at least one discovered path containing both an inversion witness and a searchability/continuity witness.
- [ ] Step 4: Report discovery-path count and distinguish it from equality quotient count.
- [ ] Step 5: Preserve the explicit `newNonredundantTheoremCount = 0` declaration unless a genuinely new Agda theorem is added and proved.

### Task 3: Verification gate

**Files:**
- No production source changes beyond Tasks 1–2.

- [ ] Step 1: Run the relevant Agda theorem-graph command from `flake.nix`.
- [ ] Step 2: Run Mercury graph discovery and e-graph saturation.
- [ ] Step 3: Run the existing theorem-registry reconciliation.
- [ ] Step 4: Run agda2hs extraction separately, ensuring inversion remains downstream of Agda semantics.
- [ ] Step 5: Review the final diff and report any unavailable compiler/CI evidence explicitly.

---
