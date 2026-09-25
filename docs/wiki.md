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

## MARL-facing laws and Hodge-Maxwell composition

The closed learner-side composition is `CanonicalMARLLawCompositionTheorem`. It groups the exact recurrent-prefix law, F4 step law, NormPair step invariance, and the endogenous Watkins target into the existing full GRU × F4 × NormPair × Watkins composition.

The physics-facing Law I/II/III vocabulary remains a separate semantic layer: agent dynamics, local Maxwell field equations, and variational/virtual-work constraint. The theorem surface does not infer a physical learner interface merely from those names; an explicit representation and transition-conjugacy witness is required.

The carrier-polymorphic Hodge-Maxwell representation is exposed by `ContinuousHodgeMaxwellExactRepresentationData` and `ConnectedContinuousHodgeMaxwellGRURepresentationTheorem`. The latter carries exact differential-form field equations, encode/decode inversion, step conjugacy, continuity obligations, a global StateIsomorphism, and encoder injectivity.

The full-learner bridge is `CanonicalLearnerHodgeMaxwellCompositionTheorem`. It consumes the closed MARL composition together with an explicit learner↔solution inverse pair and exact learner-step/Hodge-step conjugacy. Its derived `canonical-learner-hodge-maxwell-step-conjugacy` theorem transports the canonical learner transition into the Hodge-Maxwell representation.

The bridge is intentionally not classified as an unconditional existence theorem. The unconditional promotion is the closed MARL composition and the learner-side F4/NormPair results; Hodge-Maxwell composition becomes an exact theorem once its explicit representation witness is supplied.

## Why Mermaid, and what it is not

Mermaid is a diagram-description DSL, not a pure typed functional programming language. A flowchart source names nodes, edges, labels, subgraphs, and presentation/layout directives; the Mermaid parser and renderer turn that declarative description into a diagram. The official syntax is organized around diagram types such as flowcharts, sequence diagrams, class diagrams, state diagrams, and ER diagrams. It has no role as proof authority and does not replace Agda's type system. Mermaid fits this repository because the topology is a human-readable graph projection that fits Markdown/GitHub documentation. Tcl or Lua could generate a graph, but that would make the repository own an unnecessary general-purpose program and runtime semantics instead of keeping the topology as a directly readable graph declaration. The choice is therefore about representation fit, not language-theoretic superiority.

## What the F4 ray actually says

The F4 ray theorem is an exact statement about the implemented discrete update under a specified persistent forcing pattern: the selected integer-valued optimizer coordinate advances by a fixed nonzero increment, hence grows linearly with the horizon. It is not a theorem that “F4 is an optimizer that diverges,” and it is not a convergence result in the opposite direction. The important boundary is persistent forcing plus the exact update rule.

That mechanism is not unique in the broad sense. Adam uses adaptive first- and second-moment estimates; Lion uses signed momentum; IDBD adapts per-feature learning rates; and Zap-Q uses stochastic-approximation / matrix-gain machinery. These are materially different update mechanisms. Persistent nonzero increments or other sustained forcing can produce unbounded drift in many algorithms. What is specific to this repository is that the F4/L2 recurrence, its integer carrier, and the linear-growth consequence are all stated and checked exactly on the canonical learner. The optimizer comparison is about update mechanics, not a claim that these algorithms have identical dynamics or convergence behavior.

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

## Evidence-format policy

JSON is the machine-readable evidence/interchange layer and Mermaid is the human-readable topology projection. TSV and CSV are not canonical graph stores. SQLite is unnecessary for the current repository-local deterministic workload, and NoSQL is even less justified because there is no distributed, schema-flexible, high-write query problem to solve. Dhall remains the verification contract and is executed inside Nix where that existing unattended path needs it.

A CSV used by an unrelated replication archive is a separate artifact and is not part of the topology format policy.

## Source hierarchy

1. Agda definitions and proofs.
2. Dhall verification contract.
3. Current graph artifacts.
4. This wiki and README.
5. Historical notes only as provenance; they are not current semantics.

## Maintenance rule

Any theorem deletion, proof-boundary change, or new economic bridge must update the Agda source, graph, Dhall gate, README, and this wiki in the same change. Stale historical claims are pruned rather than preserved as if they were current results.
