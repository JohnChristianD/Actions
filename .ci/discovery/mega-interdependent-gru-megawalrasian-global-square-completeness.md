# Mega-interdependent GRU–MegaWalrasian global-square completeness

```mermaid
flowchart LR
  X["Economic state X"] -->|generalized equilibrium| E["Equilibrium E"]
  X -->|global encode F| H["GRU carrier H"]
  H -->|readout R| X2["Economic state X′"]
  E -->|aggregate / equilibrium projection| E2["Equilibrium E′"]

  subgraph SQ["Global square"]
    X --> H
    H --> X2
    X --> E
    E --> E2
    H --> E2
  end

  C["Conjugacy witness<br/>R ∘ F = id / commuting dynamics"] --> I["Injectivity witness"]
  I --> T["Equilibrium-preserving transport"]
  T --> W["Welfare adapter"]
  W --> P["Pareto witness"]

  H --> C
  E --> T
  E2 --> T
  X2 --> C

  P --> Q["For every qualifying generalized equilibrium:<br/>ParetoOptimal(aggregate equilibrium allocation)"]

  Q --> G["GLOBAL COMPLETENESS"]
  I --> G
  C --> G
  T --> G

  N["No separate Arrow–Debreu / KKT / Walrasian nodes"] --> E

  M["Monotonicity/local nonsatiation is an<br/>assumption for a welfare implication,<br/>not an equilibrium↔Pareto identity"] --> W
  S["Second-welfare-style reverse direction<br/>requires additional assumptions; monotonicity alone is insufficient"] --> W

  classDef core fill:#edf7ed,stroke:#5a8f5a,stroke-width:2px;
  classDef proof fill:#e8f0ff,stroke:#356ac3,stroke-width:2px;
  classDef warn fill:#fff4db,stroke:#b27a00,stroke-width:2px;
  classDef final fill:#e7f7ef,stroke:#31805a,stroke-width:3px;
  class X,H,X2,E,E2,N core;
  class C,I,T,W,P proof;
  class M,S warn;
  class Q,G final;
```

## Completion invariant

[
mathrm{Complete}
iff
egin{array}{l}
	ext{every square has a proof of commutation/conjugacy,}\
	ext{every encoded carrier map needed for recovery is injective,}\
	ext{equilibrium transport preserves the generalized equilibrium predicate,}\
	ext{the welfare assumptions are instantiated, and}\
	ext{the resulting Pareto witness is transported to the composed object.}
end{array}
]

The economic direction is deliberately one-way at the First Welfare Theorem stage:

[
mathrm{Equilibrium}landmathrm{WelfareAssumptions}
Rightarrow
mathrm{ParetoOptimal}.
]

It is not encoded as

[
mathrm{Equilibrium}iffmathrm{ParetoOptimal}
]

unless a separate reverse theorem and its assumptions are formally supplied.
