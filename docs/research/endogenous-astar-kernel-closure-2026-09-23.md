# Endogenous A* kernel-checked closure — 2026-09-23

The obsolete `Fin n` representation-transport layer is now followed by a
carrier-polymorphic theorem graph in which e-graph equality composition and
A* cost-guided traversal are one semantic closure rather than unrelated
branches.

## Canonical edge

`CanonicalAStarCostGuidanceTheorem`
→ `CanonicalEndogenousEGraphAStarTransportClosureTheorem`

The closure consumes:

- the Agda-certified A* zero/successor cost identities;
- `EqualityCompositionTheorem`, which is the proof-relevant equality-composition
  seam corresponding to equivalence-space/e-graph composition;
- the exact canonical token-logit trace composition, making the search trace
  endogenous to the recurrent learner;
- `GeneralizedRepresentationTransportCompositionTheorem`;
- `ExactFunctionIsomorphismTransportTheorem`.

Mercury's `semantic_law` graph supplies the discovered equivalence/dependency
space and its A* traversal; Agda supplies the exact equality-composition and
transport terms. Thus e-graph discovery and A* are coupled at the discovery
boundary while proof authority remains in Agda.

No `Fin n` action/state cardinality is introduced by this closure.

## Proof authority

The new closure is a constructor-backed Agda theorem. Its dependencies are
ordinary Agda terms, so the claimed kernel check is the Agda `--safe` gate,
not a synthetic Mercury edge. Mercury remains the equality-saturation/discovery
layer.

## Boundary

This theorem does not assert that arbitrary A* heuristics are optimal, nor does
it turn the graph search into a probabilistic or analytic result. It certifies
the exact cost algebra and exact endogenous token-trace composition that the
repository's A* dependency search can consume.

The prior finite probability/belief surfaces remain separate where finite
support is part of the mathematics.
