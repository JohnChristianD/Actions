# E-Graph / A* convergence closure — 2026-09-27

## Intent

Add the next proof seam after the existing semantic e-graph/A* closure: a typed, conditional convergence witness that makes the missing termination assumption explicit instead of treating A* cost or graph membership as convergence evidence.

## Current proof boundary

The theorem authority remains `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`.

The existing `AStarSemanticClosure` and `UnconditionalAgdaEGraphAStarClosure` establish semantic equality from a sound `EGraphSemanticPath`. The new `EGraphAStarFiniteRankConvergenceWitness` adds a bounded `Nat` rank, a strict-descent obligation outside the stable region, an eventual-stability witness, persistence of stability, and a semantic path from every stable candidate to the target.

The resulting `eGraphAStarConvergenceSemanticClosure` theorem proves an eventual semantic equality witness:
`Σ n, interpret (candidate (iterate step n s)) ≡ interpret target`.

This is intentionally a conditional convergence closure. It does not claim that the repository's concrete e-graph implementation already has a finite state bound, nor that arbitrary rewrite systems or A* searches converge.

## Mathematical split

```text
A* cost / heuristic
        |
        v
   search ordering
        |
        v
candidate path -----> e-graph semantic path -----> semantic equality
        |
        v
finite/bounded Nat rank + strict descent
        |
        v
eventual stable state
        |
        v
e-graph/A* semantic convergence closure
```

A* remains operational guidance. E-graph soundness remains the equality authority.

## Evidence

Agda's standard library provides well-founded induction over `Nat`'s strict order, so a future concrete instance can replace the supplied `eventualStable` field with a derived termination theorem once the repository exposes the required finite/bounded state-space invariant.

## Non-goals

- No unconditional convergence theorem for arbitrary e-graphs.
- No claim that A* optimality implies semantic equality.
- No GRU convergence claim.
- No new programming language or runtime dependency.

## Verification target

The focused proof is the safe Agda check for `TheoremsMonolith.agda`, followed by the repository's e-graph/A* CI gates. If those checks are unavailable, the change remains an explicit conditional interface rather than a claimed verified implementation.


## Concrete LayerNorm instantiation

The generic conditional closure is now instantiated for the canonical integer LayerNorm expression family by a three-phase finite-rank normalization state: `raw -> centered -> radicand`.

The concrete witness is `integerLayerNorm-egraph-astar-finite-rank-witness`. Its rank is 2/1/0 across those phases, strict descent holds outside the radicand phase, and the radicand phase is stable under the step. The resulting `integerLayerNorm-egraph-astar-eventual-semantic-closure` supplies eventual semantic equality to the radicand target.

The infinite-horizon statement is phrased as an eventual stable index followed by persistence:
`Σ n, ∀ k, stable (iterate k (iterate n phase))`.
This avoids conflating eventual stabilization with boundedness or a metric contraction property.

The concrete proof uses the existing `integerLayerNormAStarClosure` and its e-graph semantic interpretation. A* remains a cost/heuristic carrier; the convergence proof uses the finite rank and e-graph semantic path, not A* optimality as a semantic axiom.

This is a normalization-path theorem, not an unconditional convergence theorem for arbitrary e-graph rewrite systems or arbitrary A* searches.


## Certified path composition extension

The next e-graph seam is now explicit: eGraph-path-trans composes two typed EGraphSemanticPath witnesses into one path. The LayerNorm raw-to-radicand path now consumes the existing certified raw-to-centered and centered-to-radicand edges through their typed path fields rather than reconstructing the two edges manually.

This keeps the semantic seam narrow: certified edge metadata remains descriptive, EGraphSemanticPath remains the equality witness, and path composition is structural recursion over the proof object. A* still supplies cost/heuristic guidance rather than semantic truth.

Knowledge delta:
- Exotic/ERL/FullCoupled/TheoremsMonolith.agda: generic typed e-graph path composition and LayerNorm composition now share one proof mechanism.
- docs/research/egraph-astar-convergence-2026-09-27.md: records the composition seam and its proof boundary.
- .ci/actions_ci.dhall: CI gate will require the new path-composition theorem.
