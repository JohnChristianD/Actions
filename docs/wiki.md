# Repository Wiki — current semantic state

This page is the compact knowledge layer for the current repository state. It replaces the stale historical narrative with the semantics that are actually present on `main`.

## What the project proves

The canonical learner is a coupled recurrent state machine. Its exact definitions expose:

- recurrent state and scan composition;
- Watkins state and endogenous target construction;
- F4/L2 optimizer state;
- LCB counts and sparse policy readout;
- q-log control/value state;
- preserved `NormPair`;
- exact clock growth;
- integer-token recurrent processing;
- exact linear Haar mixing.

The theorem monolith derives exact structural consequences from those definitions.

## What emerges without extra economic assumptions

The current closed theorem core establishes:

- exact recurrent composition laws;
- state-isomorphism/transport interfaces;
- absence of nontrivial finite cycles for the full canonical state;
- `NormPair` preservation;
- `NormPair` quotient/factor transition;
- policy and transition factorization through that quotient;
- exact F4 optimizer stability;
- an exact F4 unit-forcing growth ray;
- no unconditional infinite-horizon upper bound for that F4 quantity;
- a closed singleton generalized-Walrasian empty-equilibrium countermodel.

The central composition theorem is `CanonicalF4NormPairUnconditionalFactorStabilityTheorem`.

## What does not emerge automatically

None of the learner-side results alone proves:

- convergence;
- existence of a fixed point;
- market clearing;
- a supporting/derived price;
- generalized Walrasian equilibrium existence;
- Arrow–Debreu existence;
- First Welfare or Second Welfare conclusions without their economic hypotheses.

This is a semantic boundary, not a missing “final theorem.” The absence is intentional and is supported by the closed countermodel and by the exact non-fixed-point clock law.

## Production-side topology

The production-side contract uses standard economic vocabulary:

```
CompetitiveProductionEconomy
  -> feasible production plans
  -> profit-maximizing production
  -> consumer optimality
  -> aggregate resource balance
  -> market clearing
  -> derived/supporting price
  -> generalized Walrasian equilibrium
```

The contract records the data and conditions of a competitive equilibrium. It is not an unconditional existence theorem.

## Welfare boundary

Competitive equilibrium can support a First Welfare direction only under the usual demand/preference assumptions encoded by the relevant theorem surface.

A Second Welfare direction is a separate supporting-price/redistribution statement. Pareto optimality alone does not manufacture the required supporting-price certificate.

## Contribution boundary

The contribution is not “formalization is novel,” “Agda is novel,” or “Walrasian equilibrium was newly proved.”

The research contribution is the mechanically auditable dependency topology showing, for this coupled learner, which conclusions are exact consequences and where independent economic assumptions must enter.

## Source hierarchy

1. Agda definitions and proofs.
2. Dhall verification contract.
3. Current graph artifacts.
4. This wiki and README.
5. Historical notes only as provenance; they are not current semantics.

## Maintenance rule

Any theorem deletion, proof-boundary change, or new economic bridge must update the Agda source, graph, Dhall gate, README, and this wiki in the same change. Stale historical claims are pruned rather than preserved as if they were current results.
