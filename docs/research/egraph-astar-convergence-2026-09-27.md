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
