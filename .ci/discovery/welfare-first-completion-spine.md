# Welfare-first completion spine

This is the first completion path for the mega-interdependent GRU–MegaWalrasian composition.

```mermaid
flowchart TD
  E["Walrasian / generalized equilibrium witness"]:::eq
  A["Explicit welfare assumptions"]:::ass
  A1["Local nonsatiation / appropriate monotonicity"]:::ass
  A2["Feasibility + market clearing"]:::ass
  A3["Budget optimality / no affordable strict improvement"]:::ass
  A4["Preference interpretation sufficient for Pareto comparison"]:::ass
  A --> A1 --> A2 --> A3 --> A4

  FWT["First Welfare Theorem adapter"]:::thm
  PE["Pareto-optimal allocation witness"]:::thm
  ALL["For every equilibrium witness satisfying the adapter assumptions"]:::quant
  DYN["Dynamic / GRU / POMDP equilibrium inherits Pareto witness"]:::goal

  E --> ALL
  A4 --> ALL
  ALL --> FWT --> PE
  PE --> DYN

  I["Interdependent-preference checkpoint"]:::warn
  I --> FWT
  Q["Important: interdependence alone does not imply Pareto efficiency;<br/>the welfare theorem's assumptions must be proved for the chosen preference model."]:::warn
  Q --> I

  classDef eq fill:#edf7ed,stroke:#5a8f5a,stroke-width:2px;
  classDef ass fill:#eef6ff,stroke:#5580aa,stroke-width:1px;
  classDef thm fill:#e8f0ff,stroke:#356ac3,stroke-width:2px;
  classDef quant fill:#f3edff,stroke:#7a57a5,stroke-width:2px;
  classDef goal fill:#e7f7ef,stroke:#31805a,stroke-width:3px;
  classDef warn fill:#fff4db,stroke:#b27a00,stroke-width:2px;
```

The formal target is:

[
orall,p,a,; operatorname{WalrasianEq}(p,a)
land operatorname{WelfareAssumptions}(p,a)
	o
operatorname{ParetoOptimal}(a).
]

For the dynamic composition, the final bridge should quantify over the dynamic equilibrium witness and prove that its static/economic projection satisfies the same assumptions before transporting Pareto efficiency back to the composed object.
