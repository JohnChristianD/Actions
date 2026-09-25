# Actions — canonical learner, theorem, and economic dependency topology

This repository is a mechanically checked study of one coupled recurrent learner and the exact consequences that follow from its definitions. The authoritative mathematical surface is Agda; the discovery and CI layers are subordinate tooling.

The current thesis-facing claim is deliberately narrow: the formalization makes the dependency boundary explicit. Exact learner dynamics yield exact representation, quotient, factorization, and stability facts. They do not, by themselves, yield convergence, a fixed point, market clearing, supporting prices, or Walrasian equilibrium existence.

## Authoritative sources

- `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda` — canonical learner definitions and definitional laws.
- `Exotic/ERL/FullCoupled/TheoremsMonolith.agda` — theorem consumer and semantic/economic boundary.
- `.ci/actions_ci.dhall` — verification lanes and required checks.
- `.ci/discovery/` — declaration extraction, dependency discovery, and graph consistency checks.
- `docs/research/current-semantic-emergence-2026-09-25.mmd` — current end-to-end topology.
- `docs/economics/` — production/equilibrium vocabulary and economic boundary documentation.

The Agda monoliths are intentionally kept as the proof source. Graphs are explanatory and discovery artifacts; a graph edge never substitutes for an Agda proof.

## Repository-wide semantic e-graph closure

Every Agda source file in `Exotic/ERL/FullCoupled/` is now covered by the same proof-only semantic transport boundary: e-graph related expressions compose by reflexivity, symmetry, transitivity, contextual transport, rewrite transport, and explicit path closure. `EGraphSemanticTransport.agda` also carries a typed A*-style cost/heuristic model. The cost guides discovery; it never becomes a proof of equality. The exact A* learner-side cost and trace laws remain in `TheoremsMonolith.agda` as `CanonicalAStarCostGuidanceTheorem` and `CanonicalEndogenousEGraphAStarTransportClosureTheorem`.

The unconditional claim is deliberately at the graph-semantic layer: once a sound interpretation is supplied, every sound e-graph path has equal endpoints, independent of the chosen A* costs. This closure does not manufacture Maxwell Law-I/Law-III witnesses, equilibrium witnesses, or other domain-specific semantic inhabitants.

The current Agda inventory is:
- `CanonicalLearnerMonolith.agda` — canonical learner definitions.
- `TheoremsMonolith.agda` — canonical theorem and semantic boundary surface.
- `EGraphSemanticTransport.agda` — proof-only e-graph and A*-cost transport kernel.
- `FourLawClosureWitnesses.agda` — explicit physical witness contracts.
- `FourLawClosureImpossibility.agda` — generic non-derivability boundary for those contracts.
- `GRUStatisticalInjectivity.agda` — canonical statistical/injectivity adapter.
- `TsallisStatisticalRepresentation.agda` — carrier-polymorphic statistical representation kernel.
- `CanonicalGamePorts.agda`, `CanonicalClosedLoopBench.agda`, `CanonicalFaithfulGameVariants.agda`, and `AdditionalBenchmarkPorts.agda` — benchmark/environment support surfaces.

The monoliths remain the proof authority. Auxiliary Agda files are not independent theorem authorities; their semantics enter the common transport layer through explicit typed terms.

## Current semantic emergence

The current closed learner-side path is:

```
canonical learner definitions
        |
        v
exact recurrent scan / composition
        |
        +--> NormPair preservation and quotient factorization
        |
        +--> F4 optimizer stability
        |          |
        |          +--> exact unit-forcing growth ray
        |          +--> no unconditional infinite-horizon F4 upper bound
        |
        v
F4 × NormPair unconditional factor-stability theorem
        |
        +--> representation/factor information
        |
        +--> does NOT imply convergence
        +--> does NOT imply a fixed point
        +--> does NOT imply market clearing
        +--> does NOT imply supporting prices
        +--> does NOT imply Walrasian existence
```

The economic side is a separate assumption boundary:

```
competitive production economy
        -> feasible firm production plans
        -> profit-maximizing production
        -> consumer optimality / demand
        -> aggregate resource balance
        -> market clearing
        -> derived/supporting price
        -> generalized Walrasian equilibrium
```

That chain is a semantic contract/topology, not an unconditional existence proof. Classical Arrow–Debreu/Walrasian existence requires the economic hypotheses that make the relevant fixed-point, compactness, convexity, continuity, preference, production, and separation arguments available.

## Exact learner facts

The canonical learner state contains the recurrent learner channels, optimizer state, counts, q-log state, and `NormPair`.

The current closed facts include:

- the canonical step increments the Nat clock exactly once;
- every positive iterate changes the clock, hence there is no nontrivial finite cycle of the full canonical state;
- `NormPair` is preserved by the canonical transition;
- the policy is invariant under `NormPair` replacement and optimizer replacement;
- the `NormPair` replacement relation is an equivalence relation;
- policy, one-step transition, and iterated transition factor through the `NormPair` quotient;
- `CanonicalNormPairQuotientFactorTransitionTheorem` packages that factor transition;
- `CanonicalF4GlobalOptimizerStabilityTheorem` is closed;
- `CanonicalF4NormPairUnconditionalFactorStabilityTheorem` packages F4 stability with NormPair factorization;
- the exact F4 unit-forcing ray gives linear growth and therefore rules out an unconditional infinite-horizon upper bound for that F4 quantity;
- the generalized Walrasian countermodel is closed, including a singleton semantic model with no equilibrium witness and the corresponding universal non-existence result.

These are exact consequences of the current definitions. They are not empirical claims.

## Economic boundary

The theorem monolith exposes standard literature-facing names for:

- generalized Walrasian equilibrium;
- competitive production economies;
- production sets and feasible firm plans;
- profit-maximizing production;
- consumer optimality and feasibility;
- aggregate resource balance;
- market clearing;
- supporting/derived prices;
- welfare interfaces.

The production side is intentionally contract-level. It records what a competitive production equilibrium would contain; it does not manufacture an equilibrium witness.

The same boundary is enforced on the negative side: the empty-equilibrium countermodel demonstrates that the learner-side factor-stability result cannot be used as an unconditional generalized-Walrasian existence theorem.

## Contribution framing

The thesis does **not** claim novelty from:

- using machine-checked mathematics;
- using Agda rather than Lean;
- restating classical Walrasian or welfare theorems;
- calling a quotient/factor construction a new general abstraction theory.

The intended contribution is the explicit, mechanically auditable dependency boundary for this coupled model:

```
exact learner laws
  -> representation / factor structure
  -/-> convergence
  -/-> fixed point
  -/-> market clearing
  -/-> supporting price
  -/-> equilibrium existence
```

The production-side vocabulary is aligned with established formal-economics terminology, while the learner/economic interface records exactly where independent economic assumptions enter.

## Toolchain roles

Agda is the proof authority. The monoliths are checked with:

```sh
$AGDA_COMMAND --safe -l standard-library -i . Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
$AGDA_COMMAND --safe -l standard-library -i . Exotic/ERL/FullCoupled/TheoremsMonolith.agda
```

Mercury extracts declarations and searches dependency candidates. Dhall declares the verification contract and is rendered/executed inside the Nix development environment where that existing unattended path needs it. Nix supplies the reproducible environment. GitHub Actions executes the declared lanes.

The graph evidence stack is intentionally minimal: JSON is the machine-readable evidence/interchange layer; Mermaid is the human topology projection. TSV and CSV are not canonical topology formats. SQLite or NoSQL is not warranted for the current deterministic, repository-local dependency workload; add a database only if a demonstrated query/history workload exceeds what the JSON evidence and normal shell tooling can do.

The orchestration arrows are not mathematical implication arrows.

## MARL, Hodge-Maxwell, and optimizer semantics

The repository now promotes one closed MARL-facing composition: `CanonicalMARLLawCompositionTheorem`. It packages the recurrent-prefix law, the exact F4 step law, NormPair step invariance, the endogenous Watkins target law, and the already-closed `CanonicalGRUF4NormWatkinsPrefixCompositionTheorem`.

The physics-level Law I/II/III grouping is kept distinct from that closed learner theorem. Law I describes agent dynamics, Law II the local Maxwell field equations, and Law III the variational/virtual-work constraint. Their composition with the learner therefore requires an explicit physics→learner representation/transition witness; those physical equations are not silently inferred from the learner algebra.

The exact Hodge-Maxwell representation surface is carrier-polymorphic: `ContinuousHodgeMaxwellExactRepresentationData` supplies the differential-form equations, solution carrier, encode/decode inverse laws, transition closure, recurrent conjugacy, and continuity obligations. `ConnectedContinuousHodgeMaxwellGRURepresentationTheorem` packages the resulting StateIsomorphism, field equations, and global encoder injectivity.

`CanonicalLearnerHodgeMaxwellCompositionTheorem` is the chosen full-learner bridge. It composes the closed MARL theorem with an explicit Hodge-Maxwell representation and explicit learner↔solution inverse/step-conjugacy witnesses. Its derived `canonical-learner-hodge-maxwell-step-conjugacy` theorem transports the exact learner step into the Hodge-Maxwell representation. This bridge is deliberately proof-relevant rather than an unconditional existence claim.

The exact `f4-unit-forcing-linear-growth` theorem is a persistent-forcing result: a specified unit forcing produces linear growth in the selected integer-valued F4 coordinate. This is not unique to F4 as a mathematical mechanism—constant nonzero increments produce linear drift for many update rules—but the exact discrete F4/L2 forcing ray is a property of this implementation and is what the Agda proof establishes.

## Graph discipline

The current graph separates:

1. definitions;
2. exact algebraic/recurrent emergence;
3. quotient/factor structure;
4. F4 stability and growth boundary;
5. economic interpretation gates;
6. production-side equilibrium topology;
7. welfare implications.

A graph node is not promoted to a theorem merely because it is useful for search. Candidate edges must be backed by the actual Agda surface.

## Scope boundaries

The repository contains additional exact formal substrates, including integer-token recurrent processing, finite probability/POMDP structures, and linear Haar/sparsemax components. These are kept separate from the economic existence boundary.

No claim is made that the learner is empirically optimal, that the formal production economy exists for arbitrary inputs, or that deterministic non-fixed-point dynamics exclude stationary distributions of a separately defined stochastic process.

## Verification policy

The CI contract must check the current theorem names and current graphs only. Historical theorem partitions, deleted convergence transports, deleted certificate-only existence routes, and stale README inventories are not authoritative and must not be reintroduced as gates.

When documentation and source disagree, the Agda source and the current Dhall verification contract are authoritative; the documentation must then be corrected to match them.

The repository no longer treats `docs/wiki.md` as a canonical source; the README, theorem monolith, CI contract, and focused research notes are the maintained knowledge surface.
