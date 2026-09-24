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