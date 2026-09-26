# Actions — canonical learner, theorem, and economic dependency topology

This repository is a mechanically checked study of one coupled recurrent learner and the exact consequences that follow from its definitions. The authoritative mathematical surface is Agda; the discovery and CI layers are subordinate tooling.

The current thesis-facing claim is deliberately narrow: the formalization makes the dependency boundary explicit. Exact learner dynamics yield exact representation, quotient, factorization, and stability facts. They do not, by themselves, yield convergence, a fixed point, market clearing, supporting prices, or Walrasian equilibrium existence.

## Authoritative sources

- `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda` — canonical learner definitions and definitional laws.
- `Exotic/ERL/FullCoupled/TheoremsMonolith.agda` — theorem consumer and semantic/economic boundary.
- `.ci/actions_ci.dhall` — verification lanes and required checks.
- `.ci/discovery/` — declaration extraction, dependency discovery, and graph consistency checks.
- `docs/research/current-semantic-emergence-2026-09-25.mmd` — current end-to-end topology.
- `docs/research/theorem-improvement-completion-2026-09-26.md` — completed theorem-improvement search and proof-boundary note.
- `docs/economics/` — production/equilibrium vocabulary and economic boundary documentation.

The Agda monoliths are intentionally kept as the proof source. Graphs are explanatory and discovery artifacts; a graph edge never substitutes for an Agda proof.

## Repository-wide semantic e-graph closure

All surviving Agda modules are covered by the same proof-only semantic transport boundary through `RepositorySemanticEGraphClosure.agda`: an indexed semantic family supplies one sound interpretation per module, and every sound e-graph path closes to exact endpoint equality. `EGraphSemanticTransport.agda` supplies reflexive, symmetric, transitive, contextual, rewrite, and explicit path transport plus a typed A* cost/heuristic model. The A* cost guides traversal; it never becomes evidence for equality. The learner-side A* seam remains in `TheoremsMonolith.agda` as `CanonicalAStarCostGuidanceTheorem` and `CanonicalEndogenousEGraphAStarTransportClosureTheorem`.

This is the repository's **full unconditional semantic e-graphed closure**: unconditional over every supplied indexed Agda semantic family, every module in that family, and every sound path. It is not an unconditional claim that every physical or economic theorem is inhabited. In particular, it does not manufacture Maxwell Law-I/Law-III witnesses, equilibrium witnesses, or other domain-specific semantic inhabitants.

The current Agda inventory is:
- `CanonicalLearnerMonolith.agda` — canonical learner definitions.
- `TheoremsMonolith.agda` — canonical theorem and semantic boundary surface.
- `EGraphSemanticTransport.agda` — proof-only e-graph and A*-cost transport kernel.
- `FourLawClosureWitnesses.agda` — explicit physical witness contracts.
- `FourLawClosureImpossibility.agda` — generic non-derivability boundary for those contracts.
- `CommonsComposition.agda` — nested/self-similar commons preservation boundary and counterexample.
- `GRUStatisticalInjectivity.agda` — canonical statistical/injectivity adapter.
- `GRUFractalInjectiveComposition.agda` — generic level/refinement/transport kernel for GRU-injective fractal composition.
- `GRUFractalInjectiveCompositionCanonical.agda` — canonical Nat-indexed scale-invariant GRU instantiation.
- `GRUFractalDomainAdapters.agda` — Physics/Economics proof-relevant adapter contracts.
- `GRUFractalLimitClosure.agda` — arbitrary-limit approximation/separation closure boundary.
- `GRUFractalEGraphAStarLimitComposition.agda` — derives limit separation/injectivity from a surviving left inverse and reuses the proof-only e-graph/A* soundness kernel.
- `GRUFractalLimitDecoderSurvival.agda` — derives a limit left inverse from coherent finite decoder projections.
- `ZPFStatisticalRepresentation.agda` — typed ZPF/ω³ Maxwell-statistical boundary and conditional global ZPF→GRU injectivity adapter.
- `TsallisStatisticalRepresentation.agda` — carrier-polymorphic statistical representation kernel.
- `RepositorySemanticEGraphClosure.agda` — repository-wide indexed semantic-family closure over e-graph paths and A* guidance.

The monoliths remain the proof authority. Auxiliary Agda files are not independent theorem authorities; their semantics enter the common transport layer through explicit typed terms.

### Complete surviving-Agda closure index

The repository-wide semantic closure is indexed by an explicit finite `RepositoryAgdaModule` enumeration containing every surviving `Exotic/ERL/FullCoupled/*.agda` file. The closure theorem quantifies over that complete index and an externally supplied sound semantic family. This makes the scope claim auditable: no surviving Agda file is outside the semantic e-graph/A* boundary.

The exact chain is:

    all surviving Agda files
      -> supplied sound module interpretation
      -> sound e-graph path
      -> A*-guided traversal
      -> exact semantic endpoint equality

The word **unconditional** applies to this graph-semantic theorem after its typed soundness input is supplied. It does not assert unconditional physical Maxwell existence. The nLab/Noether and Euler-Lagrange interfaces close the semantic obligations as explicit inputs; the repository still refuses to invent a Law-I trajectory/current equality, a Law-III action/variation/stationarity inhabitant, or the learner↔Maxwell inverse/step witness.

## Source-grounded Maxwell semantic boundary

The Maxwell semantic adapters are aligned with the external mathematical semantics rather than treating search artifacts as proofs. nLab's Noether treatment connects variational symmetries with on-shell conserved currents; its conserved-current entry defines horizontal closure on the dynamical shell. nLab's Maxwell and Hodge-Maxwell entries provide the differential-form equations and the Hodge-theoretic existence/uniqueness statement under its stated hypotheses. nLab's action-functional and Euler-Lagrange entries connect action critical loci with equations of motion, including Maxwell's equations.

The Stanford Encyclopedia of Philosophy's gauge-theory entry independently records the modern Maxwell variables, current conservation, the Lagrangian/Euler-Lagrange route to Maxwell's equations, and the Noether correspondence between classical Lagrangian symmetries and conserved currents. Wikipedia supplies accessible cross-checks for Maxwell charge conservation, Euler-Lagrange field equations, and the electromagnetic tensor/Lagrangian formulation. The Tsallis source surface describes Tsallis entropy as a one-parameter generalization of Boltzmann-Gibbs-Shannon entropy and emphasizes nonadditivity; Wikipedia documents the q-statistical construction and its q-logarithm/q-exponential relations.

These sources justify the semantic shape of the adapters. They do not provide the repository-specific discrete current-preservation equality, learner↔Maxwell inverse, or learner-step conjugacy. Those remain explicit typed obligations in NLabMaxwellSemanticClosure; no external source is imported as an Agda axiom.

The maintained primary-source audit is docs/research/four-law-primary-source-closure-audit-2026-09-25.md. The focused ZPF/ω³ implementation note is docs/research/zpf-omega3-gru-statistical-law-2026-09-25.md.

<!-- BEGIN GENERATED DOCUMENTATION INDEX -->

Generated from the tracked Markdown surface: 33 files.
The root README is the GitHub-facing entry point; detailed evidence remains in the linked source documents. Internal CI/discovery notes and historical agent plans are intentionally excluded from this public documentation index.

### Economics

- [Economic e-graph: emergent-only Arrow–Debreu](docs/economics/economic-egraph-emergent-arrow-debreu.md)
- [Economic A*-E-Graph Target: No Primitive Economic Price](docs/economics/economic-egraph-no-primitive-price.md)
- [F4 / NormPair / economic unconditionality boundary](docs/economics/f4-normpair-economic-unconditionality-boundary-2026-09-24.md)

### Research

- [Adaptive sparsemax action-domain redesign — 2026-09-23](docs/research/adaptive-sparsemax-action-domain-2026-09-23.md)
- [Carrier-polymorphic frontier closure — 2026-09-26](docs/research/carrier-polymorphic-frontier-2026-09-26.md)
- [Complete connected theorem graph closure — 2026-09-22](docs/research/complete-connected-theorem-graph-2026-09-22.md)
- [Endogenous A* kernel-checked closure — 2026-09-23](docs/research/endogenous-astar-kernel-closure-2026-09-23.md)
- [2026-09-23 finite-carrier transport promotion](docs/research/finite-carrier-transport-promotion-2026-09-23.md)
- [Four-law primary-source closure audit — 2026-09-25](docs/research/four-law-primary-source-closure-audit-2026-09-25.md)
- [Graph closure audit — 2026-09-23](docs/research/graph-closure-audit-2026-09-23.md)
- [GRU automata/sign-optimizer graph research](docs/research/gru-automata-signoptimizer-graph.md)
- [GRU fractal domain adapters — 2026-09-26](docs/research/gru-fractal-domain-adapters-2026-09-26.md)
- [GRU-injective fractal composition — 2026-09-26](docs/research/gru-fractal-injective-composition-2026-09-26.md)
- [GRU fractal arbitrary-limit closure — 2026-09-26](docs/research/gru-fractal-arbitrary-limit-closure-2026-09-26.md)
- [Unbounded Int8 integee-eing upgeade — 2026-09-23](docs/research/int8-unbounded-z-ring-2026-09-23.md)
- [Int8 vocabulary boundary and recurrent closure — 2026-09-22](docs/research/int8-vocabulary-recurrent-closure-2026-09-22.md)
- [F4 horizon-indexed rounding-bias residual regret boundary](docs/research/jensen-minimax-rounding-kkt-markov-bound.md)
- [Law IV carrier-polymorphic Tsallis audit — 2026-09-25](docs/research/law-iv-tsallis-carrier-polymorphic-2026-09-25.md)
- [Learner equivalence class: algebraic and computational boundary](docs/research/learner-equivalence-class.md)
- [MARL-facing laws, Hodge-Maxwell composition, and the F4 growth ray](docs/research/marl-laws-hodge-maxwell-f4-ray-2026-09-25.md)
- [Algebraic proof: nonlinear sequence storage and generation](docs/research/nonlinear-sequence-storage-generation-algebra.md)
- [NormPair quotient/factor transition closure](docs/research/normpair-factor-transition-closure-2026-09-24.md)
- [Strict unconditional theorem graph for the full monolith](docs/research/strict-unconditional-theorem-graph-2026-09-25.md)
- [Theorem composition improvements — 2026-09-26](docs/research/theorem-composition-improvements-2026-09-26.md)
- [Theorem-improvement completion — 2026-09-26](docs/research/theorem-improvement-completion-2026-09-26.md)
- [Theorem improvement frontier — 2026-09-26](docs/research/theorem-improvement-frontier-2026-09-26.md)
- [Unconditional canonical-price non-derivability — 2026-09-26](docs/research/theorem-no-unconditional-canonical-price-derivation-2026-09-26.md)
- [Unconditional tragedy-of-the-commons non-derivability — 2026-09-26](docs/research/theorem-unconditional-commons-nonderivability-2026-09-26.md)
- [Thesis contribution reassessment against the dedicated literature — 2026-09-25](docs/research/thesis-contribution-reassessment-2026-09-25.md)
- [Thesis nomenclature and topology review — 2026-09-25](docs/research/thesis-literature-topology-production-welfare-2026-09-25.md)
- [Unconditional finite-candidate price kernel — 2026-09-26](docs/research/unconditional-finite-price-kernel-2026-09-26.md)
- [ZPF ω³ / GRU statistical law boundary — 2026-09-25](docs/research/zpf-omega3-gru-statistical-law-2026-09-25.md)

### Repository documentation

- [Econlib stationary-Markov equilibrium graph](docs/econlib-stationary-markov-graph.md)
- [Stationary-distribution / finite-cycle obstruction graph](docs/stationary-cycle-impossibility-graph.md)

<!-- END GENERATED DOCUMENTATION INDEX -->

### Current frontier synchronization — 2026-09-26

The current carrier/policy/frontier surface is documented in:
- [Carrier-polymorphic frontier closure — 2026-09-26](docs/research/carrier-polymorphic-frontier-2026-09-26.md)
- [.ci/discovery/carrier-polymorphic-frontier-2026-09-26.mmd](.ci/discovery/carrier-polymorphic-frontier-2026-09-26.mmd)

The canonical learner's `Int8` representation is an unbounded `ℤ` wrapper, not a `Fin n` carrier. Generic cross-domain representation laws are `Set`-polymorphic; genuinely finite theorem surfaces may still use `Fin n` where finiteness is part of the proposition.

The behavior-policy topology distinguishes the exact sparsemax weight readout (`BehaviorPolicy : Nat → SparseWeight`) from the selected-action `canonicalPolicy`. No probability-normalization or full information-set behavioral-strategy theorem is inferred without an explicit adapter.

The theorem-improvement completion adds a reusable strict relation, factor-transition and step-conjugacy transport kernels, explicit production/equilibrium assumption witnesses, a distributional stationary-aggregate bridge, and proof-carrying e-graph edge metadata. The remaining factor and economic bridges stay explicitly witness-gated; no new unconditional convergence or equilibrium theorem is inferred.

Finite-cycle exclusion is factored through the generic `StrictProgressWitness`: the clock is sufficient but not conceptually necessary. The canonical learner has a clock-free instantiation through strictly increasing `totalCount`.

The four-law closure remains witness-gated: Law-I, Law-III, and physics→learner transition inhabitants are prerequisites, not consequences of the learner algebra. The economics frontier remains separately gated by convergence, fixed-point, market-clearing, price-support, and equilibrium witnesses.


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

The canonical learner state contains the recurrent learner channels, optimizer state, counts, q-log state, and `NormPair`. Its `Int8` name is an unbounded `ℤ` wrapper in the current definition; it is not a `Fin n` carrier.

The current closed facts include:

- the canonical LCB `totalCount` increments exactly once per canonical step;
- every positive iterate strictly increases that count, hence there is no nontrivial finite cycle of the full canonical state;
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

The production-side vocabulary is aligned with established formal-economics terminology, while the learner/economic interface records exactly where independent economic assumptions enter.\n\nThe exact policy topology now separates `canonicalBehaviorPolicy : Nat → SparseWeight` from the selected-action `canonicalPolicy`. The cross-domain representation layer remains `Set`-polymorphic, while genuinely finite theorem surfaces may retain `Fin n` where finiteness is part of the proposition.

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

The ZPF layer is now formalized separately in `ZPFStatisticalRepresentation.agda`: it records homogeneous, isotropic, stochastic Maxwell-field semantics, an explicit ω³ spectral-density law contract, and a ZPF→canonical-GRU statistical representation. Its global injectivity theorem is derived from the existing decode-after-encode kernel; no concrete physical ZPF realization or numerical spectral normalization is asserted by the Agda file.

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

## Scheduled commit-totality README refresh

The repository has a deterministic README refresher. The Dhall surface renders the updater script; the Nix flake exposes it as `slow-readme-update`; and the scheduled GitHub workflow runs it against `main`. The updater records every commit since the previous processed commit rather than sampling an arbitrary recent window.

<!-- BEGIN RECENT COMMIT TOTALITY -->
last-processed-commit: eedf6149a7ba9ee43e76e86fbd0716449d570efd
unprocessed-commit-count: 3

The scheduled updater accounts for every commit since the previous processed commit.
ascii-safe-commit-subjects: true

- `eedf6149a7ba` rebase: GRU fractal domain adapters onto main
- `09ce4e0a0abb` rebase: canonical price non-derivability onto main
- `9c1d6059677d` docs: refresh README from commit totality
<!-- END RECENT COMMIT TOTALITY -->
