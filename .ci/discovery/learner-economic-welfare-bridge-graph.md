# Exact learner–economic–welfare connected bridge

```mermaid
flowchart LR
  L["CanonicalFullLearnerState"] -->|toEconomic| E["Economic solution state"]
  E -->|fromEconomic| L
  L -->|canonicalFullStep| L2["Learner next state"]
  E -->|economicStep| E2["Economic next state"]
  L2 -->|toEconomic| E2

  I["Exact inverse laws<br/>fromEconomic(toEconomic s)=s<br/>toEconomic(fromEconomic x)=x"] --> ISO["StateIsomorphism"]
  C["Step conjugacy<br/>toEconomic(learnerStep s)=economicStep(toEconomic s)"] --> ITER["Exact finite-horizon conjugacy"]
  ISO --> ITER
  E -->|equilibrium| EQ["Economic equilibrium"]
  L -->|transport| LEQ["Learner equilibrium"]
  LEQ -->|inverse transport| EQ
  EQ -->|welfare assumptions| P["Pareto optimal"]
  E --> P
  HM["Connected Hodge-Maxwell/F4/Watkins bridge"] --> L
  HM --> C
  ITER --> G["FULL CONNECTED LEARNER → ECONOMIC → WELFARE BRIDGE"]
  LEQ --> G
  P --> G
```

The proof path is semantic: the existing Hodge-Maxwell/F4/Watkins theorem supplies exact learner dynamics; the economic theorem supplies an actual state isomorphism and step conjugacy; welfare is then transported through the economic equilibrium relation.

Canonical Agda nodes:

- `megaEconomicSolutionStateIsomorphism`
- `megaEconomicSolutionStepConjugacy`
- `megaEconomicSolutionEquilibriumTransport`
- `connectedCanonicalLearnerEconomicWelfareCompositionTheorem`
- `connectedHodgeMaxwellLearnerEconomicWelfareBridge`

The composition is conditional on the supplied economic interpretation, inverse laws, step conjugacy, equilibrium transport, and welfare implication; it does not identify arbitrary learners with economies.

## Policy–Hodge-Maxwell update seam

```mermaid
flowchart LR
  S["CanonicalFullLearnerState"] --> R["canonicalPolicy<br/>LCB + Watkins + Sparsemax"]
  R --> PS["policy-induced update"]
  S --> LS["canonicalFullStep"]
  PS -->|policyStepCorrect| LS
  LS -->|Hodge-Maxwell encode| M["Hodge-Maxwell solution"]
  M -->|exact step| M2["next Maxwell solution"]
  PS -->|policy-to-Maxwell commuting square| M2
  LS -->|canonical Maxwell conjugacy| M2
```

The new Agda seam is `policyHodgeMaxwellUpdateSeam`, with the canonical specialization `policyHodgeMaxwellCanonicalUpdateSeam`. The specialization proves that if the supplied policy-induced update is extensionally the canonical learner step, then the existing Maxwell step conjugacy transports that update exactly to the Hodge-Maxwell solution step.

This closes the graph edge that was previously only described as a missing boundary. It is still conditional: the graph does not infer that every LCB/Watkins/Sparsemax readout induces the learner transition. `policyStepCorrect` is the explicit proof obligation for that computational interpretation.
