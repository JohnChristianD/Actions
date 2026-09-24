# Economic e-graph: emergent-only Arrow–Debreu

This graph treats Arrow–Debreu as a derived specialization, never as a primitive semantic node. The former gate module has been removed. The remaining interface records only an actual derivation of the classical conditions.

## Rule

An Arrow–Debreu label may enter the e-graph only when the derivation has established the classical structural conditions that make the specialization meaningful. Merely having a generalized Walrasian equilibrium, a KKT characterization, a price, or market clearing is not sufficient.

## Canonical semantic spine

EconomicStructure -> FeasibleAllocations -> PreferenceChoice -> Production -> IndividualOptimality -> DemandAndSupply -> AggregateResourceBalance -> MarketClearing -> DerivedPriceOrDualCertificate -> GeneralizedWalrasianEquilibrium

Arrow–Debreu is an interpretation/specialization edge:

GeneralizedWalrasianEquilibrium + finite-dimensional commodity structure + own-bundle consumer preferences + classical budget/ownership structure + convexity/continuity assumptions required by the chosen theorem + competitive production/profit-maximization structure + classical feasibility/market-clearing conditions -> ArrowDebreuSpecialization

The graph must NOT contain a free-standing ArrowDebreuEquilibrium node.

## Emergence criterion

Arrow–Debreu is retained only if a downstream theorem genuinely requires the conjunction of classical assumptions above, or if a specialization theorem explicitly consumes those assumptions and returns the classical Arrow–Debreu statement.

If no theorem consumes those assumptions, the Arrow–Debreu class is eliminated as redundant.

## Forbidden rewrites

GeneralizedWalrasian -> ArrowDebreu
KKT -> ArrowDebreu
MarketClearing -> ArrowDebreu
Price -> ArrowDebreu
ParetoOptimal -> ArrowDebreu
WholeAllocationPreference -> ArrowDebreu
EquilibriumWitness -> ArrowDebreu

These rewrites are invalid without the missing hypotheses.

## Implementation status

The unused specialization scaffolding has now been removed. There is no Arrow–Debreu Agda node on this branch. The monolith now also contains an Econlib-style minimal First Welfare derivation kernel: strict-preference costliness plus the budget cost bound derive the no-strict-affordable-alternative clause, which then feeds the existing Pareto contradiction. The cost bounds themselves remain explicit inputs because the generalized carrier does not yet encode local nonsatiation, demand correspondence, or a concrete commodity-space cost model.

## Economic closure target

primitive economic structure -> feasible/production structure -> preference/choice structure -> demand/supply witnesses -> aggregate balance -> dual/separation/fixed-point certificate -> derived price -> market clearing -> generalized equilibrium -> welfare/existence consequences

Only after a classical specialization path is actually established may the e-graph expose ArrowDebreuSpecialization.

## Why this is stricter

The repository currently states that Walrasian, Arrow–Debreu, and KKT are not separate semantic nodes and that the canonical equilibrium relation is generalized. This document preserves that design while making the Arrow–Debreu boundary an explicit e-graph policy: classical Arrow–Debreu appears only as an emergent consequence of explicit specialization assumptions.

## Proof-obligation order

1. Close preference/choice structure.
2. Derive the demand-side cost bounds from the concrete budget and local-nonsatiation/demand model.
3. Use those bounds to derive no-strict-affordable-alternative and prove First Welfare.
4. Close production and profit-optimal supply where production is present.
5. Close feasibility and aggregate resource balance.
6. Derive individual demand/supply.
7. Derive market clearing.
8. Derive the price/dual certificate rather than treating supporting price as unexplained economic input.
9. Establish the generalized equilibrium witness.
10. Add the Arrow–Debreu specialization edge only if the classical assumptions have been proved.
11. Keep Arrow–Debreu absent otherwise.

The objective is not to make the theory less general. It is to prevent a classical label from becoming a hidden primitive.


## 2026-09-24 closure graph update

The finite consumer side now has an explicit chain:

Finite non-IID equilibrium witness -> concrete budget-cost bound -> demand-cost kernel -> no-strict-affordable-alternative -> First Welfare Pareto optimality.

The next missing steps are now typed rather than implied:

Production primitives -> feasible firm plans -> profit-optimal supply -> aggregate resource balance -> market clearing.

In parallel, the price side remains:

Convex/separation/fixed-point certificate -> derived price -> generalized equilibrium.

The repository does not yet prove those frontier edges. The new FiniteCompetitiveProductionClosure record captures the minimum production/profit/resource-balance witness without importing a new library or creating a separate economic theorem module. EconomicEquilibriumClosureGraph records the remaining dependency edges explicitly so the e-graph cannot collapse them into Arrow-Debreu, KKT, price, or market-clearing identities.

Current closure status:

- Proven: finite demand-cost -> First Welfare.
- Witnessed: finite non-IID equilibrium -> generalized equilibrium.
- Added seam: production/profit/resource balance.
- Frontier: supply+demand -> market clearing.
- Frontier: separation/fixed point -> derived price.
- Frontier: derived price+clearing -> generalized equilibrium existence.
- Frontier: classical assumptions -> Arrow-Debreu specialization.
