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


### Automated end-to-end graph gate

The closure graph is now checked in CI through the existing Dhall/Nix orchestration. The gate verifies that the canonical Mermaid graph contains the required economic nodes and that the theorem monolith exposes the corresponding production, clearing, derived-price, generalized-equilibrium, and classical-specialization seams.

The gate emits `.ci/discovery/economic-closure-graph.json` as an observed status artifact. It checks graph/source consistency; it does not promote a frontier edge to a proved theorem.


### Monolith-wide automated frontier

The economic frontier is not limited to the production, clearing, and price seams. The canonical source is a 7,000+ line TheoremsMonolith containing a large existing surface of equilibrium, welfare, transport, conjugacy, POMDP, learner-economic composition, boundary, and existence declarations.

The automated graph therefore treats the monolith itself as the semantic inventory. CI now records:

- total record declarations and top-level theorem/data declarations;
- the subset matching economic, equilibrium, welfare, production, demand, supply, market, price, POMDP, closure, transport, conjugacy, and composition concepts;
- boundary/counterexample records;
- composition/transport/isomorphism records;
- the semantic-law count and dependency evidence produced by the existing Mercury theorem e-graph;
- the explicit economic frontier edges.

The resulting artifact is .ci/discovery/economic-closure-graph.json, while the detailed declaration inventories are emitted as CI discovery artifacts. The graph does not infer that a declaration is a proof merely because its name contains a theorem word. The Agda-safe monolith remains the proof authority, and the Mercury e-graph remains dependency evidence.

The frontier status vocabulary is now explicit:

- PROVED: an actual Agda derivation exists and is consumed by the graph.
- CONDITIONAL: the conclusion follows after explicit supplied hypotheses.
- FRONTIER: the dependency is identified but the required derivation is not yet present.
- BLOCKED-BY-COUNTEREXAMPLE: an existing boundary/counterexample prevents promotion without additional hypotheses.

This keeps existing counterexamples and boundary records inside the automated graph rather than treating them as irrelevant failures. It also means the next closure pass can search the whole existing theorem surface for compositions before adding another seam.

### Topological fixed-point existence route

The monolith now closes a concrete conditional existence path using declarations that already exist on the exact import surface:

```
TopologicalConvergenceWitness
  -> FixedPointExistenceFromConvergence
  -> fixed-point witness
  -> GeneralizedWalrasianFixedPointClosure
  -> GeneralizedWalrasianExistence
```

The transport variant reuses the existing `StateIsomorphism`, `isomorphismIterateConjugacy`, and fixed-point transport machinery before applying the same economic bridge:

```
topological fixed point
  -> exact state transport
  -> transported fixed point
  -> generalized Walrasian existence
```

This is a real Agda derivation, but it is deliberately conditional. It does not claim Brouwer or Kakutani from the learner's discrete topology. The convergence witness and the fixed-point-to-equilibrium bridge remain explicit proof inputs. The unattended graph can therefore promote this route as a proved conditional composition while keeping classical convex/separation existence as a separate frontier.

The architecture remains unchanged: economic proofs stay in TheoremsMonolith.agda; CanonicalLearnerMonolith.agda remains the intentionally separated learner source.


### End-to-end single-pass unattended unconditional target

The complete target graph is now explicit:

```
Economic primitives
  -> demand + competitive supply
  -> aggregate balance + market clearing
  -> economic update operator
  -. exact GRU/F4 representation .-> GRU-F4 economic injectivity
  -> convergence from economic assumptions
  -> TopologicalConvergenceWitness
  -> FixedPointExistenceFromConvergence
  -> fixed-point witness
  -> fixed-point -> equilibrium from economic primitives
  -> GeneralizedWalrasianExistence
```


The finite-rank stability seam is also now an actual Agda bridge: `topologicalConvergenceWitness-from-finite-rank-stability` transports eventual exact fixation into the existing convergence-witness interface while keeping the convergence relation explicit.

The GRU/F4 injectivity seam is now an actual Agda composition. `gruf4EconomicInjectivityFromGlobalSquare` combines the existing F4/NormPair/GRU global observation injectivity with `MegaWalrasianGlobalSquareConjugacy` injectivity. It is supporting evidence for the dynamics path, not a replacement for the convergence proof: injectivity alone does not establish convergence.

The two edges marked `FRONTIER` are the only local mathematical gaps in this target route:

1. `economic update operator -> TopologicalConvergenceWitness`: the repository currently has convergence/fixed-point witness types, but no theorem deriving convergence from the economic primitives.
2. `fixed-point witness -> GeneralizedWalrasianFixedPointClosure`: the current bridge is a supplied record, not a theorem deriving equilibrium from primitive economic assumptions.

The existing conditional route remains closed:

```
TopologicalConvergenceWitness
  -> FixedPointExistenceFromConvergence
  -> GeneralizedWalrasianFixedPointClosure
  -> GeneralizedWalrasianExistence
```

Therefore this branch deliberately does not relabel the unconditional target as proved. The unattended graph is complete, while CI must keep the target blocked until both frontier proofs are present.

The cross-repository Econlib existence theorem is also an evidence source, not a local proof. The CI cross-repository check confirms that `Economy.exists_equilibrium` exists upstream, but the local generalized/interdependent allocation semantics still require an explicit adapter before that result can be promoted into the local Agda proof authority.


The finite-rank convergence seam has a concrete boundary on the canonical learner state. The theorem `canonicalFullLearner-no-finite-rank-stability` proves that the full canonical learner state cannot itself carry a `FiniteRankStabilityCertificate`: its exact clock increment prevents any one-step fixed point. Therefore the eventual-absorption certificate needed by the convergence bridge must be formulated on an invariant quotient or factor that intentionally removes the nonstationary clock coordinate. This is a concrete obstruction and design requirement, not a convergence proof.


The stationary-law route is now explicit as an alternative frontier. `StationaryLimitTheorem` already provides a conditional pattern in which a distribution-valued orbit converges and the transition preserves its limit, yielding stationarity. `MarkovStationaryWalrasianCompositionTheorem` then supplies a `StationaryWalrasian` lift from a static Walrasian aggregate. What is still missing for the MARL/Hodge-Maxwell/GRU-F4/Norm-Pair composition is the actual neighborhood stationary-law witness, including explicit probability/distribution semantics and its connection to the economic aggregate. The repository's existing boundary is deliberate: deterministic F4/Norm-Pair stability does not itself manufacture a probability law or measure-theoretic convergence theorem.


## Policy quotient refinement: NormPair is dynamically inert

The closure audit now distinguishes two replacement facts. Both `NormPair` and F4 optimizer replacement preserve the instantaneous `canonicalPolicy`, but only `NormPair` is dynamically inert in the canonical learner transition. The new theorem `canonicalFullStep-replaceNorm` proves definitionally that replacing the norm before a step is equal to stepping first and replacing the preserved norm afterward.

This makes the `NormPair` coordinate a genuine quotient candidate: policy observation and canonical transition both respect norm replacement. F4 optimizer replacement remains policy-invariant at a fixed state, but optimizer state enters `canonicalEndogenousFeedback` and `canonicalOptimizerStep`, so optimizer replacement is not yet a valid dynamic quotient merely from policy invariance.

The stationary-law route should therefore quotient out `NormPair` first, while treating optimizer state as a policy-hidden but dynamically active coordinate. No convergence or stationary-law existence claim is added by this refinement.


The quotient seam is now iterated, not only one-step: canonicalFullStep-replaceNorm-iterate proves by induction that replacing NormPair before any finite canonical orbit is equal to replacing the preserved norm after the orbit. This is the reusable dynamic compatibility law needed before defining a quotient/factor transition. It still says nothing about convergence or stationary-law existence, and it does not extend to optimizer replacement because optimizer state remains dynamically active.

## Finite/discrete candidate-price closure

A new constructive kernel, `finiteCandidatePriceSearch`, can classify a finite supplied price-candidate list at a fixed allocation when an explicit decision procedure for the supporting relation is provided. This is a finite search/classification result, not an Arrow–Debreu or Walrasian existence result.

The derivation graph therefore keeps the kernel below the supporting-price frontier: it can consume an already decidable supporting relation, but it does not derive that relation from separation, KKT, fixed-point, or classical convexity hypotheses.
