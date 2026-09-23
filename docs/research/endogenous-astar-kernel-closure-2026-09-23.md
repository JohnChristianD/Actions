# Endogenous A* kernel-checked closure — 2026-09-23

The obsolete `Fin n` representation-transport layer is now followed by a
carrier-polymorphic theorem graph and a new endogenous A* closure.

## Canonical edge

`CanonicalAStarCostGuidanceTheorem`
→ `CanonicalEndogenousAStarTransportClosureTheorem`

The closure consumes:

- the Agda-certified A* zero/successor cost identities;
- the exact canonical token-logit trace composition, making the search trace
  endogenous to the recurrent learner;
- `GeneralizedRepresentationTransportCompositionTheorem`;
- `ExactFunctionIsomorphismTransportTheorem`.

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
