# Expanded generalized aggregate excess demand e-graph — 2026-09-28

## Purpose

This note records the next economic e-graph layer after representation injectivity and the existing conditional convergence/fixed-point/Walrasian composition.

The new seam is deliberately reduced-form and proof-relevant:

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

The composition node couples this economic kernel to an existing `EGraphSemanticPath`. The path remains semantic equality evidence; the economic kernel remains explicit witness evidence.

## Literature-facing requirements

Standard general-equilibrium treatments use aggregate excess demand as a reduced-form object whose zeros characterize equilibrium. The classical production/consumption formulation also separates individual optimization from aggregate market-clearing conditions. Arrow and Debreu's 1954 paper explicitly treats an integrated production, exchange, and consumption economy and describes equilibrium through demand, supply, and market-equilibrium conditions.

For the aggregate excess-demand function, the Sonnenschein–Mantel–Debreu literature identifies continuity, homogeneity of degree zero, and Walras' law as central structural restrictions in the standard exchange-economy setting. The formal kernel therefore records these three properties as independent predicates rather than deriving them from injectivity, e-graph reachability, or equilibrium labels.

This distinction is important: an abstract `Price → ExcessDemand` function in the repository is not automatically a classical Euclidean excess-demand function. The carrier-specific meanings of continuity, homogeneity, Walras' law, aggregation, and subtraction must be supplied by an explicit adapter.

## Expanded dependency graph

```
EconomicStructure
  |
  +--> individual demand witness
  |
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

## Relation to representation injectivity

Representation injectivity is orthogonal to aggregate-excess-demand regularity.

```
representation reconstruction
  -> representation injectivity
``

and

```
individual choice/supply
  -> aggregation
  -> excess demand
  -> equilibrium root
``

are separate branches. A faithful representation can transport a previously proved economic predicate when a suitable transport theorem exists; it cannot manufacture continuity, Walras' law, market clearing, a supporting price, or a root.

This preserves the repository's existing distinction:

```
representation fidelity
  != economic identification
  != excess-demand regularity
  != equilibrium existence
  != dynamic convergence
```

## Relation to Sonnenschein–Mantel–Debreu

The e-graph should not turn SMD into a theorem that every formal aggregate-excess-demand carrier satisfies arbitrary classical properties. The literature result is itself conditional on a classical economic/price-space setting.

Conversely, the formal presence of continuity, degree-zero homogeneity, and Walras' law should not be read as enough to derive uniqueness, stability, or a particular adjustment dynamic. The SMD literature is specifically relevant because these aggregate restrictions leave substantial freedom in the shape of excess demand.

The repository therefore records regularity as a required witness, not as a hidden simplification of the learner representation.

## Production-side relation

The existing production-side witness vocabulary remains upstream:

```
ProductionFeasibilityWitness
FirmProfitOptimalityWitness
ConsumerOptimalityWitness
ConsumptionFeasibilityWitness
AggregateFeasibilityWitness
MarketClearingWitness
SupportingPriceWitness
```

The new aggregate-excess-demand layer does not delete those contracts. It adds a function-level representation of the route from individual demand/supply to a reduced-form excess-demand object.

The intended future adapter is:

```
consumer optimality + firm profit optimality
  -> demand/supply functions
  -> aggregate demand/supply
  -> excess demand
```

That adapter is not yet claimed by the current generic kernel.

## Existence and dynamics boundary

The repository already has a conditional route:

```
TopologicalConvergenceWitness
  -> fixed point
  -> generalized Walrasian existence
```

The expanded aggregate-excess-demand kernel is compatible with that route but does not replace it.

A future dynamic theorem would need an explicit price/state update operator and a theorem connecting its fixed points to zeros of aggregate excess demand. Convergence of that operator would remain a separate obligation.

In particular:

```
excessDemand p = zero
  -/-> convergence of a price adjustment process
```

and

```
continuous + homogeneousZero + WalrasLaw
  -/-> uniqueness or stability
```

are intentionally not present as e-graph rewrites.

## Status

PROVED at the formal interface level:
- typed demand witness;
- typed firm-supply witness;
- typed aggregation adapter;
- typed excess-demand definition;
- explicit regularity witness;
- explicit root-to-clearing/support/equilibrium closure;
- e-graph semantic-path composition of the economic kernel.

CONDITIONAL:
- every root produces the bundled economic consequences, because those implications are explicit fields of the kernel.

FRONTIER:
- deriving the aggregate demand/supply functions from the existing optimization contracts;
- deriving continuity, degree-zero homogeneity, and Walras' law from a concrete classical commodity/price model;
- deriving a root from economic primitives;
- deriving supporting prices from separation/KKT/fixed-point assumptions;
- deriving dynamic convergence from an economic update operator.

BLOCKED-BY-COUNTEREXAMPLE:
- unconditional generalized-Walrasian existence remains blocked by the repository's explicit empty-equilibrium countermodel.

## Primary literature

Arrow & Debreu (1954), *Existence of an Equilibrium for a Competitive Economy*, Econometrica 22(3), 265–290:
https://doi.org/10.2307/1907353

Sonnenschein (1973), *Do Walras' identity and continuity characterize the class of community excess demand functions?*, Journal of Economic Theory 6(4), 345–354:
https://doi.org/10.1016/0022-0531(73)90066-5

Debreu (1974), *Excess demand functions*, Journal of Mathematical Economics 1(1), 15–21:
https://doi.org/10.1016/0304-4068(74)90032-9

Mantel (1976), *Homothetic preferences and community excess demand functions*, Journal of Economic Theory 12(2), 197–201:
https://doi.org/10.1016/0022-0531(76)90073-9

A modern general-equilibrium summary records the reduced-form role of aggregate excess demand and the SMD regularity conditions:
https://personal.lse.ac.uk/GOTTLIED/publications/GE_Notes.pdf

## Knowledge delta

- `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`: adds the expanded aggregate-excess-demand witness and e-graph composition layer.
- `.ci/actions_ci.dhall`: gates the new formal symbols.
- this note: records the literature-facing semantics, dependency order, and remaining frontier.
- README: should index this note after the change.
