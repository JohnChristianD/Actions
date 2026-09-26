# Theorem-improvement completion — 2026-09-26

This pass turns the six search-backed improvement targets into proof-relevant repository surfaces without promoting any cross-domain claim that lacks its required witness.

## 1. Strict progress is factored as a reusable relation

TheoremsMonolith.agda is the sole Agda home for the strict-progress kernel: StrictProgressRelation, StrictProgressWitness, strictProgressRelation-from-witness, strictProgressWitness-from-relation, and the cycle-exclusion adapters. The former CarrierPolymorphicFrontier.agda surface is consolidated here, so the generic relation and its Nat instantiation remain available without a second theorem module.

This is deliberately not a well-foundedness theorem: finite-cycle exclusion needs transitivity plus irreflexivity of the strict relation. Well-foundedness answers a different termination question.

Agda standard library reference: Relation.Binary.Consequences (the repository keeps the theorem implementation self-contained and import-compatible).

## 2. Factor transition is now an explicit witness interface

TheoremsMonolith.agda now exposes FactorTransitionWitness, factorTransitionAfterIterate, RelationFactorTransitionWitness, and canonicalPolicyFactorTransition.

The generic interface separates the factor carrier, observation map, factor step, observation/step commuting square, relation-respecting observation, and relation preservation by the source step.

The concrete NormPair adapter remains witness-gated at the scalar factor-step seam. canonicalPolicyFactorTransition packages the already-proved NormPair invariance and step compatibility, but still requires an explicit factorStep and its commuting proof. No deterministic factor dynamics are invented from observational invariance alone.

## 3. Encode/decode commuting squares are unified

The theorem monolith now exposes StepConjugacyWitness, stepConjugacy-iterate, iteratePredicateTransport, and stepConjugacy-property-transport.

The first theorem packages a state isomorphism plus one-step commutation and transports that equality through arbitrary finite iterates. Property transport is separate, so an isomorphism is never confused with preservation of an arbitrary invariant.

## 4. Production-side assumptions are separated into named witnesses

The production/equilibrium boundary now has distinct witness records for ProductionFeasibilityWitness, FirmProfitOptimalityWitness, ConsumerOptimalityWitness, ConsumptionFeasibilityWitness, AggregateFeasibilityWitness, MarketClearingWitness, and SupportingPriceWitness.

These are contracts, not existence claims. The existing CompetitiveProductionEconomy and CompetitiveWalrasianEquilibriumWithProduction remain the economic semantics; the new records make individual assumptions independently consumable by future composition theorems.

Primary references:
- Arrow & Debreu (1954), Existence of an Equilibrium for a Competitive Economy: https://doi.org/10.2307/1907353
- KC Border, (Non-)Existence of Walrasian Equilibrium: https://www.its.caltech.edu/~kcb/Notes/Walrasian.pdf

## 5. Distributional stationarity is kept distinct from deterministic convergence

TheoremsMonolith.agda now exposes DistributionalStationaryAggregateTransport and distributionalStationaryAggregate-stationary.

The bridge consumes the existing StationaryLimitTheorem, an explicit distribution transition law, convergence witness, limit-preservation witness, and an explicit aggregate/economic-step commuting square. From those inputs it proves stationarity of the limiting economic aggregate.

No probability space, measure, weak-convergence theorem, or stationary law is silently manufactured from deterministic learner factor stability.

## 6. E-graph edges can carry certificate metadata

EGraphSemanticTransport.agda now exposes SemanticEdgeStatus, SemanticEdgeEvidence, SemanticEdgeMetadata, CertifiedEGraphEdge, and eGraph-certified-edge-sound.

The metadata records source/target identifiers, proof identifier, explicit assumptions, verification status, evidence kind, and an unconditionality flag. Equality still comes only from the typed EGraphSemanticPath; metadata alone cannot produce semantic equality.

Primary reference:
- Ramos, Hulak & de Queiroz, Checking Equality-Saturation Merge and Extraction Certificates, Archive of Formal Proofs (2026): https://devel.isa-afp.org/entries/Equality_Saturation_Checker.html
- Goens & Bhat, Equality-Saturation as a Tactic for Proof Assistants, PLDI/EGRAPHS 2022: https://pldi22.sigplan.org/details/egraphs-2022-papers/6/Equality-Saturation-as-a-Tactic-for-Proof-Assistants

## Graph policy

The completion graph records the six improvements and retains the repository status discipline: PROVED means a safe-Agda proof term exists; CONDITIONAL means an explicit semantic witness remains an input; FRONTIER means a concrete bridge is identified but not yet inhabited; BLOCKED-BY-COUNTEREXAMPLE means a stronger universal claim has a closed counterexample.

The behavior-policy surface is included explicitly: canonicalBehaviorPolicy is a separate exact weight readout from canonicalBehaviorAction and canonicalPolicy. No probability normalization or richer behavioral-strategy claim is inferred.

## Verification boundary

The source mutations are consolidated on branch theorem-monolith-prune-frontier-2026-09-26. The repository does not expose a local Agda executable in this execution environment, so authoritative kernel verification is delegated to the repository Nix/GitHub Actions gate after the final branch is opened as a draft pull request.

No theorem is considered verified merely because the text parses or the graph is internally consistent.