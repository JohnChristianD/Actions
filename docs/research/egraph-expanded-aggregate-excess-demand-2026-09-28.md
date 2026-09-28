# Expanded generalized aggregate excess demand e-graph — 2026-09-28

## Purpose

This note records the next economic e-graph layer after representation injectivity and the existing convergence/fixed-point/Walrasian composition.

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

The graph does not infer the existence of a root or convergence. Root-to-equilibrium and root-to-fixed-point edges are explicit proof-bearing implications.

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
- `GeneralizedAggregateExcessDemandFixedPointWitness`
- `expandedGeneralizedAggregateExcessDemand-fixedPoint`
- `EGraphEconomicAggregateExcessDemandFixedPointComposition`
- `eGraphEconomicAggregateExcessDemand-fixedPointClosure`
- `EGraphEconomicAggregateExcessDemandComposition`
- `eGraphEconomicAggregateExcessDemand-closure`

The new standalone module adds:

- `canonicalStationaryPriceUpdate`
- `canonicalStationaryPriceLaw`
- `UnconditionalEGraphEconomicStationaryPriceComposition`
- `unconditionalEGraphEconomicStationaryPriceClosure`
- `unconditionalEGraphEconomicStationaryPriceComposition-from-path`

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

The final four edges are direct implications from an explicit root. The kernel does not search for a root.

## Unconditional price-law closure

The previous fixed-point seam accepted `priceUpdate : Price → Price` as an input. That is useful when formalizing a specific economic adjustment process, but it leaves the unconditional core dependent on an externally supplied operator.

The new module removes that operator from the unconditional core by choosing the canonical zero-step operator:

```
canonicalStationaryPriceUpdate p = p
```

Its law is definitional:

```
canonicalStationaryPriceUpdate p ≡ p
```

and is proved by `refl`. Consequently, every certified e-graph path can be lifted to an unconditional stationary-price composition without supplying a price-update function.

This closes the *input-operator problem* at the logical level, but it deliberately does not claim that the identity operator is a classical market-clearing or excess-demand adjustment dynamic. A non-identity economic price law still requires an explicit relation between excess demand and price motion.

The distinction is:

```
unconditional stationarity
  = canonical identity update
  -> fixed point by reflexivity

economic price adjustment
  = non-identity update tied to excess demand
  -> requires an explicit economic adapter
```

This is the maximal unconditional closure available without smuggling a price-adjustment assumption into a theorem.

## Representation boundary

Representation injectivity is orthogonal to aggregate-excess-demand regularity.

```
representation reconstruction -> representation injectivity
individual choice/supply -> aggregation -> excess demand -> equilibrium root
```

A faithful representation can transport a previously proved economic predicate when a suitable transport theorem exists; it does not itself establish continuity, Walras' law, market clearing, a supporting price, or a root.

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

The repository already has an explicit convergence-to-fixed-point route:

```
TopologicalConvergenceWitness
  -> fixed point
  -> generalized Walrasian existence
```

The expanded aggregate-excess-demand kernel retains the explicit economic fixed-point seam as `GeneralizedAggregateExcessDemandFixedPointWitness`. The new unconditional module separately supplies the canonical stationary identity law.

```
excessDemand p = zero
  -> priceUpdate p = p  [when an explicit economic law is supplied]

canonicalStationaryPriceUpdate p = p
  -> canonicalStationaryPriceUpdate p ≡ p  [unconditionally]

excessDemand p = zero
  -/-> convergence of a nontrivial price adjustment process

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
- explicit root-to-fixed-point transport when an economic price law is supplied;
- unconditional canonical stationary price law;
- unconditional e-graph stationary-price composition;
- e-graph semantic-path composition;
- e-graph fixed-point composition.

CLOSED-INTERFACE:

- every supplied excess-demand root produces the bundled economic consequences through direct implications;
- every supplied excess-demand root is transported to a price fixed point when the explicit economic price-update law is supplied;
- every certified semantic path has a canonical stationary-price composition without a price-update input.

OPEN-EDGE:

- deriving demand/supply functions from optimization contracts;
- deriving continuity, degree-zero homogeneity, and Walras' law from a concrete classical price/commodity model;
- deriving a root from economic primitives;
- deriving supporting prices from separation/KKT/fixed-point assumptions;
- deriving a nontrivial dynamic price law from economic primitives;
- deriving convergence of that nontrivial price-adjustment operator.

BOUNDARY:

- generalized-Walrasian existence is not promoted here; the repository retains an explicit empty-equilibrium countermodel against the unrestricted target;
- the identity stationary law is not presented as a substitute for an economic adjustment dynamic.

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

- `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`: expanded aggregate-excess-demand witness and economic fixed-point composition.
- `Exotic/ERL/FullCoupled/CanonicalAggregatePriceLaw.agda`: unconditional canonical stationary-price operator and e-graph composition.
- `.ci/actions_ci.dhall`: existing theorem gate remains authoritative; the new module still requires CI compilation integration.
- this note: records the input-operator closure and its semantic boundary.
- README: existing index continues to expose this note.
