# Real semantic e-graph and staleness policy — 2026-09-26

The repository now distinguishes three graph objects.

1. Dependency DAG / Mermaid projection: a human-readable prerequisite and boundary view. It is not an equality proof.
2. Semantic e-graph: an equality-saturation structure whose e-classes contain theorem-composition expressions identified as equivalent only through explicit rewrite rules. Rewrites add equal alternatives; rebuild restores congruence closure; extraction chooses a representative by cost.
3. A* search frontier: a cost-guided traversal over candidate proof plans. A* changes discovery order, not semantic truth.

For this repository, an edge is proof-authoritative only when its semantic interpretation has an Agda soundness witness. CertifiedEGraphEdge records metadata, but metadata never substitutes for the typed EGraphSemanticPath.

## Freshness pruning

The current discovery runner checks named frontier targets against the current multi-module semantic-law inventory before inserting target nodes. The inventory includes the theorem monolith plus the live GRU limit-composition modules, so a theorem declared outside the monolith is not stale merely because it has a different source file. Missing names are reported as stale targets and excluded from the fresh target set rather than silently treated as current theorems.

Historical research graphs remain historical snapshots. The current semantic graph is the live projection.

## Status vocabulary

- PROVED: a typed Agda proof certificate exists.
- CONDITIONAL: a theorem is available after explicit assumptions or witnesses.
- FRONTIER: a target has a defined interface but lacks a current proof or inhabitant.
- BLOCKED-BY-COUNTEREXAMPLE: an unconditional promotion is formally refuted.

A blocked node is a guard against invalid saturation, not an ordinary dependency edge.

## Limit boundary

GRUFractalLimitConvergenceImpossibility.agda gives a finite countermodel: a constant Bool-to-Unit limit representation admits a trivial per-state witness but cannot be injective. Therefore approximation/convergence-like data alone cannot imply limit injectivity.

The arbitrary-limit closure therefore requires a surviving left inverse or equivalent separation mechanism. GRUFractalLimitConvergenceAdapter is the positive conditional composition seam.

## Current GRU limit graph

CanonicalIntegerGRUGlobalConjugateTheorem
→ finite/indexed fractal composition
→ supplied convergence witness
→ coherent limit decoder
→ surviving left inverse
→ limit separation
→ arbitrary-limit injectivity.

The missing concrete convergence/limit inhabitant remains a frontier, not an e-graph equivalence.

## Staleness rule

A theorem name appearing only in a historical graph, stale registry, or narrative note does not become an e-class merely by being mentioned. Live graph nodes must be recoverable from the current semantic inventory or explicitly marked as external evidence or frontier data.
## Unattended ownership

Dhall owns CI composition, Nix owns the reproducible execution environment, Mercury owns semantic extraction/freshness/e-graph saturation, and Agda remains the proof authority. The frontier-target list is only the set of names whose freshness is being queried; it is not the source of truth for theorem existence.
