# Economic A*-E-Graph Target: No Primitive Economic Price

Status: design target / derivation graph

This graph treats prices as derived economic certificates rather than primitive economic inputs. It does not claim that prices can be derived in every economy without assumptions. Instead, the e-graph must retain the assumptions needed for each derivation and reject unsound rewrites that manufacture prices or equilibria.

## Core principle

Do not introduce these as unexplained economic primitives:

- equilibrium price
- equilibrium allocation
- demand correspondence
- market-clearing certificate
- supporting price
- Arrow-Debreu equilibrium label

Start from the economic structure and derive certificates through explicit construction.

## Canonical semantic spine

```
EconomicStructure
  -> feasible allocations
  -> preference/choice relations
  -> budget affordability induced by a candidate valuation
  -> individual optimality
  -> aggregate excess-demand / resource balance
  -> clearing
  -> equilibrium certificate
```

The valuation/price object itself is generated only by a valid dual, separation, optimization, or fixed-point construction.

## E-classes

### Economy

```
Economy
  = Agents × Goods × Endowments × Preferences × Feasibility × Production
```

Production is optional at the generalized layer. Pure exchange is a specialization, not the foundation.

### Preference

Allow both:

```
OwnBundlePreference
WholeAllocationPreference
```

and retain an explicit witness when claiming genuine interdependence.

### Feasibility

```
FeasibleAllocation
ResourceBalance
ProductionFeasibility
```

Production side:

```
ProductionSet
ProfitOptimality
SupplyCorrespondence
```

### Choice

```
Affordable
NoStrictAffordableAlternative
IndividualOptimality
Demand
```

Demand is a derived correspondence whenever the relevant choice problem has a solution. Do not silently assume existence.

### Valuation / price

The semantic role is:

```
Price
  <- DualCertificate
  <- SupportingFunctional
  <- SeparationCertificate
  <- Optimization/KKT multiplier
  <- FixedPoint equilibrium certificate
```

These are alternative derivation paths into the same price e-class when their equivalence has actually been proved.

## Main rewrites

```
Preference + FeasibleSet + Affordability
  -> IndividualOptimality

IndividualOptimality
  -> DemandWitness

DemandWitness(agent-wise)
  -> AggregateDemand

AggregateDemand + ResourceBalance
  -> MarketClearing

IndividualOptimality + MarketClearing
  -> GeneralizedWalrasianEquilibrium
```

Price derivation:

```
ConvexChoiceProblem
  + separation assumptions
  -> SupportingFunctional

SupportingFunctional
  -> PriceCertificate

ConvexOptimization
  + constraint qualification
  -> KKTMultiplier

KKTMultiplier
  -> DualPriceCertificate
```

Existence:

```
Compact/convex feasible structure
+ continuity/closed-graph conditions
+ nonempty convex choice correspondences
+ fixed-point conditions
  -> EquilibriumExistenceCertificate
  -> equilibrium price/allocation
```

No rewrite may skip the assumptions.

## Welfare branch

```
Equilibrium
  + LocalNonsatiation
  -> ParetoOptimality
```

Reverse direction:

```
ParetoOptimality
+ Convexity
+ LocalNonsatiation
+ Feasibility structure
+ Redistribution structure
+ Separation assumptions
  -> SupportingFunctional
  -> PriceCertificate
  -> DecentralizedOptimality
  -> Equilibrium
```

Pareto optimality alone MUST NOT rewrite to a price.

## Interdependence branch

```
WholeAllocationPreference
+ own-bundle projection
+ variation in other agents' allocations
+ sensitivity/nondegeneracy witness
  -> GenuineInterdependence
```

Conversely:

```
SeparablePreference
  -> OwnBundlePreference
```

Do not equate the type-level ability to express interdependence with a proof that interdependence occurs.

## Classical specializations

Classical labels are interpretation nodes, not competing semantic foundations:

```
GeneralizedWalrasian
  + own-bundle preferences
  + classical feasibility
  + classical budget structure
  + classical production restrictions
  -> WalrasianSpecialization

WalrasianSpecialization
  + classical finite-dimensional exchange/production assumptions
  -> ArrowDebreuSpecialization
```

If the formal equivalence is not proved, these remain tagged specialization/characterization edges rather than definitional equality.

## E-graph anti-rules

Never perform:

```
ParetoOptimal -> Price
PreferenceType -> GenuineInterdependence
EquilibriumWitness -> ExistenceTheorem
KKTCharacterization -> Existence
WholeAllocationPreference -> ClassicalPreference
GeneralizedWalrasian -> ArrowDebreu
```

unless the required hypotheses are present in the same e-class proof context.

## A* cost function

Prefer rewrites that:

1. eliminate externally supplied economic certificates;
2. preserve the generalized semantic surface;
3. derive prices from dual/separation/fixed-point structure;
4. derive demand from explicit choice problems;
5. derive clearing from aggregate resource balance;
6. derive production supply from profit optimality;
7. expose rather than hide regularity assumptions;
8. make classical theories special cases instead of duplicate semantic nodes.

Penalize:

- primitive price inputs;
- primitive equilibrium inputs;
- theorem signatures that merely accept the desired economic witness;
- duplicate Walrasian/Arrow-Debreu/KKT equilibrium definitions;
- collapsing generalized preference into own-bundle preference;
- existence claims whose proof object is only a supplied equilibrium.

## Target terminal form

```
economic primitives
    -> feasible/production structure
    -> preference/choice structure
    -> derived demand and supply
    -> derived aggregate balance
    -> derived price/dual certificate
    -> derived market clearing
    -> generalized equilibrium
    -> existence / welfare consequences
```

The terminal objective is NOT "remove every mathematical primitive." Logical and mathematical foundations remain. The objective is to remove unexplained economic black-box primitives and make every economic certificate traceable to a derivation path.

## Current repo alignment

The target is designed around the repository's generalized Walrasian surface. It deliberately keeps Arrow-Debreu, KKT, and classical Walrasian formulations as specialization/characterization paths rather than adding separate equilibrium semantics.

This is a graph specification, not a claim that all derivation edges are already implemented or proved in Agda.

## Finite candidate-price classification kernel

The theorem monolith now has a constructive finite/discrete kernel, `finiteCandidatePriceSearch`, for classifying a supplied finite candidate-price list. Its result is proof-relevant: either a supplied candidate comes with a supporting proof, or every supplied candidate comes with a rejection proof.

This does not violate the no-primitive-price design. The candidate list and the supporting-relation decision procedure are explicit inputs; the kernel does not manufacture a price from primitive preferences, feasibility, production, separation, KKT, or fixed-point structure. It also does not establish that a supporting price exists outside the supplied candidate set.

Thus the semantic distinction remains:

```
finite candidate list + explicit decision procedure
    -> candidate classification
    -/-> supporting-price derivation from primitives
    -/-> unconditional equilibrium existence
```
