# Generalized Second Welfare theorem graph

```mermaid
flowchart LR
  D["MegaGeneralizedWalrasianEquilibrium<br/>aggregate + characterization + equilibrium"] --> B["characterizationBridge"]
  P["Pareto-optimal allocation"] --> SP["Supporting-price map"]
  SP --> CH["Supporting characterization"]
  CH --> B
  B --> EQ["Generalized equilibrium witness"]
  SP --> EQ
  H["Heterogeneous agents"] --> D
  I["Whole-allocation / interdependent preferences"] --> D
  EQ --> R["Σ Price (λ p → equilibrium D p a)"]
  P --> R
  N["Pareto optimality alone"] -.->|does not imply| SP
  X["Boundary countermodel<br/>empty Price + inhabited Pareto + empty equilibrium"] -.-> N
  R --> G["SECOND WELFARE GENERALIZATION"]
```

The theorem `megaSecondWelfareGeneralized` uses the single generalized Walrasian relation. The supporting-price step is the economic separation input; once it supplies a price and the generalized characterization, `characterizationBridge` derives the actual equilibrium witness.

This is stronger than merely packaging `supportingEquilibrium`: equilibrium is obtained from the generalized characterization surface. Heterogeneous and whole-allocation/interdependent preference semantics remain inside the generalized object.

The graph does not claim that Pareto optimality alone generates a supporting price. The existing boundary countermodel remains the formal non-derivability result for that weaker premise.