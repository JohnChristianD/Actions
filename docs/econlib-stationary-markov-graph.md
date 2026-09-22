# Econlib stationary-Markov equilibrium graph

The upstream stationary-Markov bridge lives in `Econlib/Equilibrium/AggregateAccounting.lean`.

## Closed graph

```text
Econlib / Probability
  FiniteMarkovChain.exists_stationary
        |
        v
  stationary law
        | explicit stationary-functional adapter
        v
Econlib / Equilibrium
  MarkovExchangeEconomy
        |
        v
  MarkovExchangeEconomy.stationaryEconomy
        |
        v
  MeasureEconomy
        +--> stationaryEconomy_marketClears
        |
        v
  MarkovExchangeEconomy.StationaryWalrasianEquilibrium
```

The independent finite-economy existence branch is:

```text
Econlib / Equilibrium / Economy
  RegularEconomy + Irreducible + nonempty agents
  + positive commodity supply
        |
        v
Econlib / Equilibrium / Existence
  Economy.exists_equilibrium
        |
        v
  Economy.WalrasianEquilibrium
```

The local Actions lift/composition branch is:

```text
Actions::staticWalrasian
        |
        v
Actions::generalizedWalrasianEquilibrium-from-static
        |
        v
Actions::markov-stationary-walrasian-composition-theorem
```

The cross-repository graph therefore has a complete node/edge inventory, but two proof boundaries remain explicit:

1. Lean `Economy.WalrasianEquilibrium` to the local Agda `staticWalrasian` requires a real cross-language type/proof adapter. A grep-based contract is not a proof of that adapter.
2. `FiniteMarkovChain.exists_stationary` does not by itself manufacture the `FiniteSupportKernel.StationaryFunctional` required by `MarkovExchangeEconomy.stationaryEconomy`; that stationary-functional construction is an explicit adapter in the graph.

The concrete upstream example `EconlibExamples/Equilibrium/MarkovStationary.lean` supplies an inhabited `StationaryWalrasianEquilibrium` for its specified economy. That example should be treated as a concrete witness, not as a general stationary equilibrium existence theorem.

The Actions CI lane now checks these exact upstream nodes and emits `.ci/discovery/econlib-crossrepo-sync.json` and `.ci/discovery/econlib-equilibrium-graph.json` at runtime.