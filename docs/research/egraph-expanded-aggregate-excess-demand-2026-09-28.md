# Expanded generalized aggregate excess demand e-graph — 2026-09-28

## Purpose

This note records the next economic e-graph layer after representation injectivity and the existing conditional convergence/fixed-point/Walrasian composition.

```
individual demand
  -> aggregate demand
individual supply
  -> aggregate supply
aggregate demand + aggregate supply
  -> aggregate excess demand
aggregate excess demand root
  -> aggregate feasibility
  -> market clearing
  -> supporting-price predicate
  -> generalized equilibrium characterization
```

The graph does not infer the existence of a root, a supporting price, convergence of a price adjustment process, or Walrasian existence.

## Formal nodes

The theorem monolith adds:

- `GeneralizedIndividualDemandWitness`
- `GeneralizedFirmSupplyWitness`
- `GeneralizedAggregateDemandSupplyWitness`
- `GeneralizedAggregateExcessDemandWitness`
- `GeneralizedAggregateExcessDemandRegularityWitness`
- `GeneralizedAggregateMarketClearingWitness`
- `GeneralizedAggregateSupportingPriceWitness`
- `ExpandedGeneralizedAggregateExcessDemandKernel`
- `expandedGeneralizedAggregateExcessDemand-closure`
- `EGraphEconomicAggregateExcessDemandComposition`
- `eGraphEconomicAggregateExcessDemand-closure`

## Literature-facing requirements

Arrow and Debreu's 1954 competitive-economy formulation integrates production, exchange, and consumption and treats supply, demand, and market equilibrium as distinct components. The aggregate-excess-demand literature then studies the reduced-form price-to-excess-demand object.

In the standard exchange-economy setting, the Sonnenschein–Mantel–Debreu literature identifies continuity, homogeneity of degree zero, and Walras' law as central structural restrictions. The formal kernel records these three properties as independent predicates rather than deriving them from injectivity or e-graph reachability.

An abstract `Price → ExcessDemand` carrier is not automatically a classical Euclidean excess-demand function. The meanings of continuity, homogeneity, Walras' law, aggregation, and subtraction must be supplied by an explicit adapter.

## Dependency graph

```
EconomicStructure
  |
  +--> individual demand witness
  +--> firm supply witness
          |
          v
  aggregate demand/supply adapter
          |
          v
  aggregate excess-demand definition
          |
          +--> continuity
          +--> degree-zero homogeneity
          +--> Walras-law predicate
          |
          v
  zero-excess-demand root
          |
          +--> aggregate feasibility
          +--> market clearing
          +--> supporting-price predicate
          +--> generalized equilibrium characterization
```

The final four edges are conditional on explicit root-to-conclusion witnesses. The kernel does not search for a root.

## Representation boundary

Representation injectivity is orthogonal to aggregate-excess-demand regularity.

```
representation reconstruction -> representation injectivity
individual choice/supply -> aggregation -> excess demand -> equilibrium root
```

A faithful representation can transport a previously proved economic predicate when a suitable transport theorem exists; it cannot manufacture continuity, Walras' law, market clearing, a supporting price, or a root.

Thus:

```
representation fidelity
  != economic identification
  != excess-demand regularity
  != equilibrium existence
  != dynamic convergence
```

## SMD boundary

The e-graph must not turn the SMD result into a theorem that every formal excess-demand carrier has classical continuity, homogeneity, or Walras-law structure. Those properties are explicit requirements here.

Conversely, supplying those three properties must not be interpreted as proving uniqueness, stability, or convergence of a price-adjustment process. The SMD literature is relevant precisely because substantial aggregate freedom remains under those restrictions.

## Production-side relation

The existing production-side vocabulary remains upstream:

```
ProductionFeasibilityWitness
FirmProfitOptimalityWitness
ConsumerOptimalityWitness
ConsumptionFeasibilityWitness
AggregateFeasibilityWitness
MarketClearingWitness
SupportingPriceWitness
```

The new layer adds a function-level route from demand/supply to a reduced-form excess-demand object. Deriving demand/supply functions from the existing optimization contracts remains a separate adapter obligation.

## Existence and dynamics boundary

The repository already has a conditional route:

```
TopologicalConvergenceWitness
  -> fixed point
  -> generalized Walrasian existence
```

The expanded aggregate-excess-demand kernel is compatible with that route but does not replace it. A future dynamic theorem needs an explicit price/state update operator and a theorem connecting its fixed points to zeros of aggregate excess demand.

```
excessDemand p = zero
  -/-> convergence of a price adjustment process

continuous + homogeneousZero + WalrasLaw
  -/-> uniqueness or stability
```

## Status

PROVED at the formal interface level:
- typed demand and supply witnesses;
- typed aggregation adapter;
- typed excess-demand definition;
- explicit regularity witness;
- explicit root-to-clearing/support/equilibrium closure;
- e-graph semantic-path composition.

CONDITIONAL:
- every supplied excess-demand root produces the bundled economic consequences because those implications are explicit witness fields.

FRONTIER:
- deriving demand/supply functions from optimization contracts;
- deriving continuity, degree-zero homogeneity, and Walras' law from a concrete classical price/commodity model;
- deriving a root from economic primitives;
- deriving supporting prices from separation/KKT/fixed-point assumptions;
- deriving dynamic convergence from an economic update operator.

BLOCKED-BY-COUNTEREXAMPLE:
- unconditional generalized-Walrasian existence remains blocked by the repository's explicit empty-equilibrium countermodel.

## Primary literature

Arrow & Debreu (1954), *Existence of an Equilibrium for a Competitive Economy*:
https://doi.org/10.2307/1907353

Sonnenschein (1973), *Do Walras' identity and continuity characterize the class of community excess demand functions?*:
https://doi.org/10.1016/0022-0531(73)90066-5

Debreu (1974), *Excess demand functions*:
https://doi.org/10.1016/0304-4068(74)90032-9

Mantel (1976), *Homothetic preferences and community excess demand functions*:
https://doi.org/10.1016/0022-0531(76)90073-9

## Knowledge delta

- `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`: expanded aggregate-excess-demand witness and e-graph composition.
- `.ci/actions_ci.dhall`: gates the new formal symbols.
- this note: literature-facing semantics and remaining frontier.
- README: indexes this note.
