# Economic e-graph: emergent-only Arrow–Debreu

This graph treats Arrow–Debreu as a derived specialization, never as a primitive semantic node.

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

## Economic closure target

primitive economic structure -> feasible/production structure -> preference/choice structure -> demand/supply witnesses -> aggregate balance -> dual/separation/fixed-point certificate -> derived price -> market clearing -> generalized equilibrium -> welfare/existence consequences

Only after a classical specialization path is actually established may the e-graph expose ArrowDebreuSpecialization.

## Why this is stricter

The repository currently states that Walrasian, Arrow–Debreu, and KKT are not separate semantic nodes and that the canonical equilibrium relation is generalized. This document preserves that design while making the Arrow–Debreu boundary an explicit e-graph policy: classical Arrow–Debreu appears only as an emergent consequence of explicit specialization assumptions.

## Proof-obligation order

1. Close preference/choice structure.
2. Close production and profit-optimal supply where production is present.
3. Close feasibility and aggregate resource balance.
4. Derive individual demand/supply.
5. Derive market clearing.
6. Derive the price/dual certificate rather than treating supporting price as unexplained economic input.
7. Establish the generalized equilibrium witness.
8. Add the Arrow–Debreu specialization edge only if the classical assumptions have been proved.
9. Keep Arrow–Debreu absent otherwise.

The objective is not to make the theory less general. It is to prevent a classical label from becoming a hidden primitive.
