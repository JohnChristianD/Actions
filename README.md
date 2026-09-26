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

All surviving Agda modules are covered by the same proof-only semantic transport boundary through `RepositorySemanticEGraphClosure.agda`: an indexed semantic family supplies one sound interpretation per module, and every sound e-graph path closes to exact endpoint equality. `EGraphSemanticTransport.agda` supplies reflexive, symmetric, transitive, contextual, rewrite, and explicit path transport plus a typed A* cost/heuristic model. The A* cost guides traversal; it never becomes evidence for equality. The learner-side A* seam remains in `TheoremsMonolith.agda` as `CanonicalAStarCostGuidanceTheorem` and `CanonicalEndogenousEGraphAStarTransportClosureTheorem`.

This is the repository's **full unconditional semantic e-graphed closure**: unconditional over every supplied indexed Agda semantic family, every module in that family, and every sound path. It is not an unconditional claim that every physical or economic theorem is inhabited. In particular, it does not manufacture Maxwell Law-I/Law-III witnesses, equilibrium witnesses, or other domain-specific semantic inhabitants.

The current Agda inventory is:
- `CanonicalLearnerMonolith.agda` — canonical learner definitions.
- `TheoremsMonolith.agda` — canonical theorem and semantic boundary surface.
- `EGraphSemanticTransport.agda` — proof-only e-graph and A*-cost transport kernel.
- `FourLawClosureWitnesses.agda` — explicit physical witness contracts.
- `FourLawClosureImpossibility.agda` — generic non-derivability boundary for those contracts.
- `GRUStatisticalInjectivity.agda` — canonical statistical/injectivity adapter.
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

Generated from the tracked Markdown surface: 25 files.
The root README is the GitHub-facing entry point; detailed evidence remains in the linked source documents. Internal CI/discovery notes and historical agent plans are intentionally excluded from this public documentation index.

### docs

- [Econlib stationary-Markov equilibrium graph](docs/econlib-stationary-markov-graph.md)
- [Economic e-graph: emergent-only Arrow–Debreu](docs/economics/economic-egraph-emergent-arrow-debreu.md)
- [Economic A*-E-Graph Target: No Primitive Economic Price](docs/economics/economic-egraph-no-primitive-price.md)
- [F4 / NormPair / economic unconditionality boundary](docs/economics/f4-normpair-economic-unconditionality-boundary-2026-09-24.md)
- [Adaptive sparsemax action-domain redesign — 2026-09-23](docs/research/adaptive-sparsemax-action-domain-2026-09-23.md)
- [Complete connected theorem graph closure — 2026-09-22](docs/research/complete-connected-theorem-graph-2026-09-22.md)
- [Endogenous A* kernel-checked closure — 2026-09-23](docs/research/endogenous-astar-kernel-closure-2026-09-23.md)
- [2026-09-23 finite-carrier transport promotion](docs/research/finite-carrier-transport-promotion-2026-09-23.md)
- [Four-law primary-source closure audit — 2026-09-25](docs/research/four-law-primary-source-closure-audit-2026-09-25.md)
- [Graph closure audit — 2026-09-23](docs/research/graph-closure-audit-2026-09-23.md)
- [GRU automata/sign-optimizer graph research](docs/research/gru-automata-signoptimizer-graph.md)
- [Unbounded Int8 integee-eing upgeade — 2026-09-23](docs/research/int8-unbounded-z-ring-2026-09-23.md)
- [Int8 vocabulary boundary and recurrent closure — 2026-09-22](docs/research/int8-vocabulary-recurrent-closure-2026-09-22.md)
- [F4 horizon-indexed rounding-bias residual regret boundary](docs/research/jensen-minimax-rounding-kkt-markov-bound.md)
- [Law IV carrier-polymorphic Tsallis audit — 2026-09-25](docs/research/law-iv-tsallis-carrier-polymorphic-2026-09-25.md)
- [Learner equivalence class: algebraic and computational boundary](docs/research/learner-equivalence-class.md)
- [MARL-facing laws, Hodge-Maxwell composition, and the F4 growth ray](docs/research/marl-laws-hodge-maxwell-f4-ray-2026-09-25.md)
- [Algebraic proof: nonlinear sequence storage and generation](docs/research/nonlinear-sequence-storage-generation-algebra.md)
- [NormPair quotient/factor transition closure](docs/research/normpair-factor-transition-closure-2026-09-24.md)
- [Strict unconditional theorem graph for the full monolith](docs/research/strict-unconditional-theorem-graph-2026-09-25.md)
- [Thesis contribution reassessment against the dedicated literature — 2026-09-25](docs/research/thesis-contribution-reassessment-2026-09-25.md)
- [Thesis nomenclature and topology review — 2026-09-25](docs/research/thesis-literature-topology-production-welfare-2026-09-25.md)
- [ZPF ω³ / GRU statistical law boundary — 2026-09-25](docs/research/zpf-omega3-gru-statistical-law-2026-09-25.md)
- [Stationary-distribution / finite-cycle obstruction graph](docs/stationary-cycle-impossibility-graph.md)
- [Unconditional Economic Closure Pass Implementation Plan](docs/superpowers/plans/2026-09-24-unconditional-economic-closure-pass.md)

<!-- END GENERATED DOCUMENTATION INDEX -->

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
last-processed-commit: 5749ffdbd7c00608d3ac73b976db7eeb5f54f3c2
unprocessed-commit-count: 769

The scheduled updater accounts for every commit since the previous processed commit.
ascii-safe-commit-subjects: true

- `5749ffdbd7c0` fix: avoid Dhall interpolation in README sync shell
- `eec101c4ae28` fix: restore standalone script shebangs
- `cefa27bf1dcf` fix: terminate Dhall text delimiters before shebangs
- `c79a155ab82c` fix: make standalone Dhall scripts valid expressions
- `0b0dc999baa8` ci: trigger README totality on updater changes
- `7997d37d8d5d` fix: execute slow README totality updater body
- `6ba6e5bbfb2d` fix: restore README commit-totality bootstrap
- `472b9f577523` docs: derive README index titles from document headings
- `01cee4f8f1e6` docs: make README index use document headings
- `2abd465a302f` ci: trigger README sync when GitHub-facing docs change
- `3741acb2a3a7` ci: make README documentation index deterministic
- `355cd1126f88` docs: populate synchronized GitHub-facing documentation index
- `9eee204d41b3` ci: gate README against Dhall documentation sync
- `c1c445304a29` ci: continuously sync README documentation index
- `d648f23dbbd6` ci: expose the Dhall README sync app
- `8ac9f03f4bd0` docs: add synchronized GitHub-facing documentation index
- `652657014051` ci: scope README sync to GitHub-facing docs
- `1f74fd0ccea7` ci: add Dhall-driven README documentation sync
- `c718a8207da5` docs: record the explicit omega-cubed proof shape
- `ab17e8f0011a` docs: clarify proof-relevant omega-cubed semantics
- `dedae651cba6` chore: keep ZPF import namespace-local in theorem monolith
- `b3ea6d392463` fix: complete ZPF global theorem frequency parameter
- `2dccec3ab48f` fix: thread frequency multiplication through the ZPF GRU contract
- `ba1d86640dc8` fix: make the ZPF omega-cubed law proof-relevant
- `c3c3d6b10df0` docs: connect the ZPF omega-cubed layer to the semantic graph
- `e6aa727fd682` docs: document the ZPF omega-cubed formalization
- `3937bd9677e0` ci: verify the ZPF omega-cubed Agda surface
- `bb78f4f95437` chore: wire ZPF omega-cubed layer into RepositorySemanticEGraphClosure.agda
- `7aaf388e319c` chore: wire ZPF omega-cubed layer into TheoremsMonolith.agda
- `aa8b0411df30` docs: record ZPF omega-cubed formalization boundary
- `33ced95321e9` feat: formalize ZPF omega-cubed GRU statistical boundary
- `37f1e40e5f79` Add single-file Maxwell four-law GRU consistency theorem
- `2256720ec947` Record complete Agda semantic closure and source-depth audit
- `782a18fc7472` Project complete Agda semantic e-graph closure
- `c187fe825058` Gate complete surviving Agda semantic closure index
- `09c8fc9fb67e` Document complete surviving Agda semantic closure index
- `67c5cd44873b` Formalize complete surviving Agda semantic e-graph index
- `43f36dff9acf` Remove duplicated AgdaSafe commands
- `a3a3d3946267` Extend semantic emergence graph to repository-wide e-graph closure
- `d39226529d38` Prune superseded Hodge-Tsallis-Walrasian bridge note
- `6240f081b826` Expand Maxwell and Tsallis primary-source audit
- `7b37dac7118b` Document full Agda semantic e-graph closure and source boundary
- `5c24a97164ec` Typecheck the complete surviving Agda semantic surface
- `d60845b856ec` Expose repository-wide Agda e-graph A* closure
- `c37725ffaa3d` Add repository-wide Agda e-graph A* semantic closure
- `3be28f3617b7` Typecheck all surviving semantic Agda modules
- `02e3055d8c15` Record repository-wide e-graph A* closure in semantic graph
- `abba328dd6dc` Preserve current main discovery registry during rebase
- `23c17acd6802` Rebase semantic closure branch onto current main
- `073033934e7b` Delete docs/wiki.md
- `df3fd0c1dacc` docs: record nLab-backed conditional four-law closure
- `1755db9ff4f8` docs: close four-law frontier at nLab-backed conditional semantics
- `b4205dd2f511` feat: add explicit Maxwell semantic closure layer
- `c5f0d2799f36` docs: normalize nLab source notes
- `70f9c9e0e32b` docs: normalize nLab source notes
- `7009637387ae` docs: refine four-law closure semantics from nLab
- `4bd65fc9ee43` docs: record nLab Maxwell closure chain
- `98d204ea62b1` docs: record Law-I current preservation blocker
- `577be6cb6971` docs: record exact Law-I current preservation blocker
- `d242e7cd7ab5` docs: record concrete Maxwell witness boundary
- `689db53d7f42` docs: normalize Maxwell witness source references
- `869cf43fa085` docs: freeze concrete Maxwell witness boundary
- `fd0ae9c94229` docs: record Maxwell witness implementation plan
- `a6e398cfc16b` docs: plan concrete four-law Maxwell witnesses
- `bcc7eb3d4145` docs: add nLab semantic candidate boundary
- `ad2ae25ef050` docs: record nLab semantics for four-law closure
- `e9977807a4b2` docs: preserve full semantic graph while refining frontier
- `fb9b473bb583` docs: document four-law semantic closure frontier
- `e0a176aeb875` docs: refine four-law semantic closure graph
- `c9b5eaaad57f` docs: use canonical iterate and prefix theorem names
- `bbc30cbab0e8` docs: add four-law semantic closure diagram
- `e09b81322ee9` docs: reconcile four-law semantic closure graph
- `2b2034172786` Document relative impossibility boundary for four-law closure
- `0389d3b40dc4` Add relative impossibility theorem for generic four-law closure
- `f86572b9b565` Record four-law transition adapter in wiki
- `de0d506a6eb8` Document four-law transition adapter boundary
- `ffad82c9835a` Add canonical physics-to-learner transition witness adapter
- `e83b07d61eb1` Add proof-only e-graph semantic transport kernel
- `4fbe87a54ae3` Add iterate and input-indexed prefix transport kernels
- `4379bc7d9a09` fix: materialize Law IV extension lines
- `c3897af415ff` docs: record carrier-polymorphic Law IV seam
- `bc5ecdc08516` docs: record Law IV carrier-polymorphic audit
- `64a7f63cad2b` feat: lift Law IV to carrier-polymorphic statistics
- `0c424ded9198` feat: add carrier-polymorphic statistical representation
- `4c3d7a2b7a3e` Connect four-law witness contract to theorem monolith
- `d6130045324c` Document explicit four-law closure frontier
- `23b561f7116f` Graph explicit four-law witness frontier contract
- `b4ddd15abb9b` Make four-law variational obligations semantic predicates
- `fca66569b616` Add typed four-law closure witness contract
- `e7514ff37c49` docs: record primary-source closure boundary
- `120888506900` docs: add primary-source four-law closure audit
- `9501cd27df81` Document promoted conjugacy iterate kernel
- `55be8fa0b75f` Promote generic iterate transport into four-law graph
- `ba046e9ba83d` Add exact iterate transport for global conjugacy
- `fc39cd324342` Align CI graph node with four-law surface
- `d4b0440684e3` Document four-law conjugacy and prefix transport continuation
- `375148bc5446` Extend four-law graph through conjugacy and prefix transport
- `f42dd9250941` Decompose four-law proof obligations
- `5664c95b6428` Refine four-law witness dependency frontier
- `f4a28a8ad4ba` Document four-physics-law graph frontier
- `4dada70b955e` Graph four-physics-law prefix and horizon frontier
- `6a3796e433fe` Fix closure round Mercury syntax
- `c37dfa5192a0` Tighten fixed-point closure round bindings
- `35ed8a4e0f66` Fix Mercury fixed-point closure signatures
- `ed7fddfa3f84` Refine fixed-point closure reporting and seed coverage
- `6f98ad413789` Add unattended A* e-graph fixed-point closure gate
- `391db200c23e` Document four-law injectivity proof boundary
- `df21fe418acb` Graph all four law injectivity boundaries
- `e6f359c50b9c` Clarify Law IV Agda proof boundary in semantic graph
- `a8971527387a` Graph Law IV GRU injectivity and algebraic consequence
- `e77ad080fd17` Expose Law IV on the theorem surface
- `a086e08d89e6` Add closed Law IV GRU statistical injectivity theorem
- `3e6d388d2cf0` Document Law IV graph-only semantic boundary
- `a4b5010561b2` Clarify Law IV graph-only Agda boundary
- `a2bcfdca67fd` Complete Law IV ZPF graph semantics on linear branch
- `e47f49100d03` Refine Law II into Hodge-Maxwell plus explicit ZPF layer
- `61fb08e2087c` Remove stale learnerKernel dependency from Hodge bridge
- `b2abf63ae908` Repair composition frontier JSON emission
- `62b9f18e56b2` Gate the promoted MARL and Hodge theorem surface
- `81ed86a7f0b3` Align wiki with promoted MARL and Hodge theorem surface
- `fa8f50aa5c81` Align README with promoted MARL and Hodge theorem surface
- `df51e92ed0c0` Promote closed MARL composition and Hodge bridge topology
- `0132b0c28a90` Repair exact MARL law and Hodge bridge dependencies
- `f732f008fec1` Restore exact MARL law composition and Hodge-Maxwell bridge
- `d8269bbd0199` Document Mermaid semantics and F4 optimizer-ray boundary
- `4baae8a4c4b2` Restore JSON semantic artifact without TSV generation
- `d91799e0a06e` Update wiki with MARL/Hodge-Maxwell and minimal evidence stack
- `b43d7fc6da2d` Document minimal topology stack and MARL/Hodge-Maxwell semantics
- `eb11331d65cd` Document MARL laws, Hodge-Maxwell composition, and F4 ray semantics
- `5161b6bd5331` Prune stale economic graph to current topology and minimal evidence stack
- `723e7bbb9b74` Extend topology with MARL laws, Hodge-Maxwell composition, and F4 ray semantics
- `bf205381df7c` Ponytail: stop publishing redundant TSV topology views
- `1f2b449185d1` Ponytail: remove redundant TSV topology projections
- `21d0e9f8ee74` Prune stale economic CI artifact vocabulary
- `814965ecf681` Sync CI gate with current theorem topology
- `3d55dd70e59a` Add current semantic emergence graph
- `68744d6019e3` Add current repository wiki knowledge layer
- `f4e41edf06e3` Prune stale README and document current semantic boundary
- `4572e027bd08` Clarify theorem emergence semantic comments
- `9d76f7f94767` Clarify canonical learner semantic comments
- `18e60d100775` Complete dedicated literature comparison and contribution boundary
- `55d00a5606e4` Reframe thesis contributions against formal economics literature
- `6d5e47139d91` Expand factor topology and production-side Walrasian vocabulary (#73)
- `9e7c41347d8f` Explicitly use rebase for Dhall AutoMerge lane (#72)
- `8d6c12842735` Fully prune active monolith to unconditional theorem core (#71)
- `57bacffd8c20` Complete NormPair quotient/factor transition closure (#70)
- `c12d48ba9e19` Document iterated NormPair quotient compatibility
- `8a7b740bf3b2` Prove NormPair replacement commutes with iterated dynamics
- `2f6fe31318a3` Document NormPair dynamic quotient boundary
- `0afcfd2311a1` Prove NormPair replacement commutes with canonical step
- `fd78d8f1ab01` Record neighborhood stationary-law route
- `1e31d600bf3d` Document stationary-law alternative route
- `602e53ad9f48` Expose stationary-law alternative closure route
- `f9528b2b15a8` Record canonical finite-rank obstruction seam
- `9b677e260b11` Document canonical finite-rank obstruction
- `0307ca5a67fb` Expose canonical finite-rank obstruction in economic graph
- `a9be09563bb6` Discover canonical finite-rank obstruction
- `d4970f1a93ed` Gate canonical finite-rank obstruction
- `de326b2fcfe8` Expose canonical learner finite-rank obstruction
- `f705923bf795` Record finite-rank bridge CI verification and frontier
- `cf05f8731a55` Document finite-rank bridge proof-term correction
- `db974aadf563` Fix finite-rank convergence equality transport
- `57c57ac6611c` docs: record finite-rank convergence bridge
- `2b07b16a83be` test: discover finite-rank convergence bridge
- `01ead4e392e5` docs: expose finite-rank convergence bridge
- `f731c803a7ce` docs: expose finite-rank convergence bridge
- `9b438254e4d3` feat: bridge finite-rank stability to convergence witness
- `3a685d0d364c` test: gate finite-rank convergence bridge
- `1bd6dd6e0fc4` docs: record GRU-F4 injectivity closure pass
- `f9e1f65bcaed` docs: record GRU-F4 economic injectivity composition
- `f0b4b5a697d3` docs: expose GRU-F4 economic injectivity seam
- `144f65bbe1c5` test: discover GRU-F4 economic injectivity bridge
- `62fb0ee23d25` feat: compose GRU-F4 and economic injectivity witnesses
- `1b495cd04263` test: require GRU-F4 economic injectivity bridge
- `57ba6b9a47a5` ci: gate unconditional economic closure status
- `b7d3691bd352` docs: expose unconditional economic closure target
- `7ba43f1d34f1` docs: expose unconditional economic closure target
- `1b4ad2d6cb62` docs: expose unconditional economic closure target
- `da9cff38aac0` docs: plan unconditional economic closure pass
- `45526fa34de6` fix: place economic closure after generalized Walrasian declarations
- `d142b8599ed5` fix: use iterate conjugacy in economic transport closure
- `37ce7a73261c` ci: gate topological economic existence closure
- `159a3cecf5c3` docs: document topological fixed-point existence route
- `124293cc1ea1` docs: expose topological fixed-point economic route
- `7cfb1f38dcb0` feat: close economic existence through topological fixed points
- `c95c703e0db2` test: require topological economic fixed-point closure
- `7183030074e5` Align TheoremsMonolith imports with CanonicalLearnerMonolith
- `9d2a7110c397` Discover iterate fixed-point transport
- `be59d2855915` Gate iterate fixed-point transport in CI
- `4526c629eef8` Reuse iterate conjugacy for fixed-point transport
- `3b03c4e9e622` Place fixed-point closure after stationary-limit theorem
- `0194fbe7c927` Gate fixed-point closure in CI
- `2b0aad515f41` Graph convergent fixed-point existence closure
- `36c153b7e293` Connect fixed points to equilibrium witnesses
- `98ffdd02fecc` Fix fixed-point transport witness fields
- `8caee72c0555` Add convergent fixed-point topology closure
- `917c97f895d5` ci: fix single-pass discovery closure
- `46fa7ccf8e96` ci: remove redundant economic graph step
- `8ee017982479` ci: fold economic graph into discovery pass
- `a8b5c988f82d` docs: graph minimal unattended economic loop
- `c99b9ff85140` ci: publish live theorem economic graph artifacts
- `ebe1f921b3dc` Document monolith-wide economic frontier automation
- `f06feb4c5683` Expand economic graph with monolith theorem surface
- `18ead947972c` Expand economic closure graph to monolith frontier inventory
- `eaf04800f9dd` Document automated economic graph gate
- `60c7ab6d5242` Register economic closure graph CI lane
- `156291c31afd` Run economic closure graph in CI
- `c714e318eef1` Automate economic closure graph verification
- `114e70312d71` Graph economic closure frontiers
- `a13dc8c53d29` Document economic closure graph frontiers
- `f2b0f333231f` Fix economic closure graph typing
- `b1b8ead8e745` Graph economic equilibrium closure frontiers
- `4c9757e7663c` Document finite non-iid welfare closure
- `718fe5dddf8f` Fix finite Pareto affordability wiring
- `779f0694d61d` Derive finite non-IID demand cost layer
- `53c133d41b20` Place Econlib welfare kernel after base theorem and add Nat transitivity
- `bd509c6c6fed` Document Econlib-style First Welfare derivation kernel
- `de783082b560` Derive First Welfare demand certificate from cost bounds
- `481f5d8f5ee7` Remove unused economic helper
- `f41c93a87009` Close finite Walrasian witness into generalized surface
- `ae97c846e77a` Enforce monolithic theorem architecture
- `70ca732a4cb0` Prune unused Arrow-Debreu e-graph scaffolding
- `0ecf893bda6c` Remove unused Arrow-Debreu specialization scaffolding
- `50012766bb4b` Document gate removal and derivation-only Arrow-Debreu seam
- `33063af972de` Remove obsolete Arrow-Debreu gate module
- `a9eae7dc92d8` Rename Arrow-Debreu gate module to specialization
- `cd65b8b32c7a` Remove redundant Arrow-Debreu gate and retain only derivation seam
- `e8ce7c1e188f` econ: add emergent-only Arrow-Debreu Agda gate
- `8dda114377cb` econ: add emergent Arrow-Debreu graph
- `1de49399738c` econ: make Arrow-Debreu an emergent-only e-graph specialization
- `73375466f2dc` Graph economic closure with derived prices and no primitive economic certificates
- `23c5593941fe` Delete Exotic/econlib directory
- `9ce2be3964a5` Delete Exotic/econlib/Equilibrium.agda
- `29f54760f7f8` docs: align second welfare graph globally
- `61673a62cc34` docs: make second welfare graph dependency exact
- `24bddf7704ea` docs: correct generalized second welfare dependency graph
- `4894493dbde7` docs: align workflow deviations with ASCII updater
- `0e110eb57161` ci: enforce ASCII README update contract
- `68ecacf00ac9` Make README commit updater ASCII-controlled
- `fa12ef46d76e` Prune and document connected composition workflow
- `e82056fce2b7` Prune README and document connected composition workflow
- `20ae18348d75` Correct policy-HodgeMaxwell closure dependencies
- `a6eeb0e99bff` Correct policy-HodgeMaxwell graph seam
- `033f6efe9201` Correct policy-HodgeMaxwell update seam
- `d37078e9d212` Document completed policy-HodgeMaxwell update seam
- `b82cc741655d` Record policy-HodgeMaxwell seam in closure graph
- `ad10d9033a52` Graph policy-HodgeMaxwell update seam
- `e0e2d2aef40c` Complete policy-HodgeMaxwell update seam
- `aa3f2d1045fd` Prune stale workflow terminology from README
- `40a6cb78caa1` Prune and document connected-theory and workflow deviations
- `184ff11b8a44` Add economic welfare bridge to closure graph
- `3f4d474bd06d` Document exact learner economic welfare bridge
- `71566f1be0da` Add connected learner economic welfare graph
- `c518a391231d` Add connected learner economic welfare graph
- `f280edae777a` Fix connected economic welfare theorem composition
- `e41f9f74f6c6` Connect economic bridge to canonical learner kernel
- `e9d2a14c61b2` Fix learner-kernel parameters in economic bridge
- `f6b9d8af7feb` Add exact learner-economic welfare bridge theorems
- `5be4ef3b3901` Prune stale README dependencies and document policy-Maxwell seam
- `546eeeb9d44d` Refine welfare and GRU-Maxwell dependency graph
- `104d03fcb4d4` Gate Second Welfare boundary symbols
- `71cafc18263f` Record Second Welfare algebraic boundary
- `d6d69d47eba5` Document completed Second Welfare theorem boundary
- `3cb36e68929b` Keep Second Welfare counterexample proposition-valued
- `c8fbcd35b294` Formalize Second Welfare theorem boundary and demand condition
- `8ca39e7fb078` docs: prune README and document connected composition workflow
- `f0ba5060de9a` Bind Pareto alternative in welfare proof
- `de38c004d2df` Make Pareto affordability bundle explicit
- `7e5721b37782` Bind Pareto improvement witness in welfare conditions
- `671c2402fdfc` Make First Welfare theorem relations explicit
- `8414147a46b9` Gate Pareto conditionality theorem surface
- `1bff25022da7` Document Pareto conditionality theorem contract
- `2807ef464d3d` Fix Pareto affordability witness binding
- `efeb33dff086` Complete global-square welfare conditionality theorems
- `22201dcf0b55` Gate global-square conjugacy injectivity completeness symbols
- `b8311a9795ce` Complete global-square formalization graph
- `b7d87e401e73` Repair global-square welfare and equilibrium transport contract
- `1ded68204661` Complete mega-interdependent GRU\u2013MegaWalrasian global-square formulation
- `b0fbe7cc767e` Update CI checks for collapsed generalized Walrasian layer
- `1b20fb136696` Add global square conjugacy and injectivity completeness graph
- `db8eb0fa2bef` Clarify collapsed generalized equilibrium contract
- `65c244c98a0a` Prune legacy equilibrium characterizations to one generalized relation
- `3cec04f00bd8` Collapse Walrasian layer to one generalized equilibrium relation
- `5d6a68f4f347` Add welfare-first completion spine to mega-Walrasian graph
- `7787c991ea96` Add rendered mega-interdependent GRU-Walrasian completeness graph
- `d1d71065aa20` Add machine-readable mega-interdependent GRU-Walrasian completeness graph
- `57e4836bee91` Add mega-interdependent GRU-Walrasian completeness graph
- `b250ed669d82` Remove specific Walrasian CI requirements
- `80885fd11393` Fix mega equilibrium witness consumer
- `0261d51a4624` Align Econlib CI with singular mega edge
- `1b929c03a376` Prune README Walrasian candidates
- `79e7ae02fdca` Prune remaining specific Walrasian candidates
- `5b0afa5c508b` Make mega equilibrium corollaries explicit
- `3a71027fa88d` Prune specific Walrasian registry dependencies
- `4ea42ad08548` Prune specific Walrasian registry dependencies
- `d7f91900d125` Prune specific Walrasian graph edges
- `4d5a6e92b2eb` Add singular mega-generalized Walrasian edge
- `f382043a524b` Clarify canonical generalized equilibrium boundary
- `d4d13f9e682a` Prune redundant Walrasian candidate metadata
- `0a5217c35628` Deduplicate mega equilibrium registry entry
- `f3cc4b8c66f8` Align registries and README with mega generalized equilibrium edge
- `40c53e7a8dc6` Align registries and README with mega generalized equilibrium edge
- `300e50615bd3` Align registries and README with mega generalized equilibrium edge
- `96b6315e98a5` Prune Walrasian candidates to one mega edge
- `c29f0d5f4f1d` Remove redundant Walrasian candidates from composition
- `6af3854dc646` Collapse Walrasian candidates into mega generalized edge
- `7da484d0c3b3` Record generalized graph head
- `7c23aaeac19e` Graph generalized Tsallis and Walrasian closure
- `b7d13d56ba33` Align Tsallis and Walrasian graph contracts
- `ab813312f9c0` Align Tsallis and Walrasian graph contracts
- `8dc694ba583c` Align Tsallis and Walrasian graph contracts
- `fcd075412ee9` Generalize Tsallis and Walrasian composition
- `a2b2d33cc6ce` Track latest unified composition head
- `7c0dbf8fc3e1` Order unified composition dependencies for Agda telescope
- `629bb740d378` Graph unified Tsallis-2 Walrasian POMDP closure
- `2abdb0cfc510` Register unified Tsallis-2 POMDP composition theorem
- `5242bec43cd3` Register unified Tsallis-2 POMDP composition theorem
- `7df9ad341568` Refine unified Tsallis-2 composition seam
- `c44cde4f8378` Compose generalized GRU Hodge-Maxwell Tsallis-2 Walrasian POMDP
- `2e89379922dc` Decouple POMDP belief semantics from observation kernel
- `c0ba84e55352` Graph Walrasian POMDP assumption relaxation
- `18269ffb83b4` Graph relaxed Walrasian POMDP surfaces
- `30c197d2be1f` Register relaxed Walrasian POMDP theorem surfaces
- `736ae3045070` Make POMDP belief policy explicit
- `1dfe4df338c0` Repair POMDP belief factorization types
- `d55d481f3b52` Generalize Walrasian equilibrium into relaxed POMDP transport
- `bd2df20e54d3` Harden theorem registry reconciler parsing
- `927c15334da5` Automate Agda-driven theorem registry pruning
- `10a88190b56c` Gate theorem registries against live Agda declarations
- `199daa378b85` Expose Agda-driven theorem registry pruning
- `6d98388a751f` Make theorem registry pruning self-verify
- `90b0d74b2301` Add Agda-driven theorem registry reconciler
- `639808ec0906` Clarify active metadata pruning policy
- `ee04e50c3aa0` Record current Maxwell generalization audit
- `32fd737d99b8` Remove retired Maxwell case metadata
- `4fc1c473ae0b` Remove retired Maxwell case metadata
- `63a570b5222a` Prune Maxwell compatibility theorem listings
- `8a1f1025341e` Prune Maxwell compatibility CI registrations
- `f3882895551f` Prune Maxwell compatibility search plans
- `f34052e0e11f` Prune Maxwell compatibility nodes from closure overlay
- `493df153ee69` Prune Maxwell compatibility nodes from graph
- `a206dc303108` Remove Maxwell finite and infinite compatibility adapters
- `8df0d228d4a8` Align Maxwell closure overlay with unified carrier theorem
- `5d146c509e57` Collapse Maxwell graph cases into unified carrier composition
- `dd654229d54b` Collapse finite and infinite Maxwell endpoints into one
- `d0c2c3b9a648` Register unified GRU-F4-Maxwell composition surface
- `2ee52aab4c6d` Register unified GRU-F4-Maxwell composition surface
- `2bbc50e03986` Register unified GRU-F4-Maxwell composition surface
- `f4e83c19eac2` Route finite and infinite Maxwell cases into unified promotion
- `36209894eaf2` Collapse Maxwell carrier cases into unified GRU-F4 composition
- `b836237d9e53` Document additional GRU-F4-Maxwell compositions
- `624deaf57133` Append GRU-F4-Maxwell theorem CI registrations
- `ed2e1ddf6559` Register additional GRU-F4-Maxwell graph searches
- `66ebe16eda73` Expand connected Maxwell closure compositions
- `889f3cd804d4` Expand GRU-F4-Maxwell connected graph compositions
- `319efe8ac863` Add finite-coordinate GRU-F4-Maxwell exact endpoint
- `6df56aebf113` Add carrier-agnostic GRU-F4-Maxwell injectivity composition
- `50f47fb37c56` Repair infinite-dimensional injectivity projection
- `f9a038e645da` Register infinite-dimensional Maxwell closure promotions
- `b026fdc00cf2` Add infinite-dimensional Hodge-Maxwell graph promotions
- `ee8b61dcbb29` Register infinite-dimensional Hodge-Maxwell graph promotion
- `6ce49bb7b9a9` Register infinite-dimensional Hodge-Maxwell graph promotion
- `e7ce23acd14a` Register infinite-dimensional Hodge-Maxwell graph promotion
- `92d05e51818c` Promote carrier-polymorphic Hodge-Maxwell to infinite-dimensional graph surfaces
- `71eec2e215c9` Document arbitrary finite-coordinate Maxwell composition
- `7942f1c1f598` Gate arbitrary finite-coordinate Maxwell composition
- `5c67e9077dbc` Discover arbitrary finite-coordinate Maxwell composition
- `307d1112b130` Synchronize arbitrary finite-coordinate Hodge-Maxwell closure
- `5542af01fd69` Graph arbitrary finite-coordinate Hodge-Maxwell composition
- `d88326f7af56` Generalize Maxwell composition over arbitrary finite coordinate dimension without Fin
- `d123c7602bd9` Fix final list-coordinate field projection
- `3036d895a4f6` Restore closure overlay and use list-coordinate Maxwell specialization
- `a7237d6d08a4` Restore graph and use list-coordinate Maxwell specialization
- `5e327bac541f` Align graph metadata with list-coordinate Maxwell carrier
- `2cac80d1f953` Align graph metadata with list-coordinate Maxwell carrier
- `15f69954e418` Remove final Fin coordinate residue from list specialization
- `e064a0b4f2f2` Use list-coordinate finite Maxwell composition surface
- `82bfb21e1a50` Use list-coordinate finite Maxwell composition surface
- `02775914d537` Use list-coordinate finite Maxwell composition surface
- `c74ae7b2f585` Use list-coordinate finite Maxwell composition surface
- `321607576722` Use list-coordinate finite Maxwell composition surface
- `71167ff99e8e` Clean up list-coordinate Maxwell specialization after carrier swap
- `ff26e56b73e1` Use list coordinates for manageable Maxwell composition carrier
- `75181d1cdd6d` Synchronize finite-dimensional Hodge-Maxwell closure overlay
- `7b17ba838a12` Document finite-dimensional Hodge-Maxwell composition surface
- `b32badf48eae` Gate finite-dimensional Hodge-Maxwell composition theorem
- `4298fdf09e98` Discover finite-dimensional Hodge-Maxwell composition theorem
- `418435950658` Graph finite-dimensional Hodge-Maxwell composed extraction
- `ca4b8a671012` Place finite-dimensional Maxwell composition after connected bridge declaration
- `864f75725226` Compose finite-dimensional Hodge-Maxwell coordinates with connected learner extraction
- `01fa4756940f` Clarify arbitrary Hodge-Maxwell solution-space injectivity scope in graph
- `1db24372dcdc` Register connected Hodge-Maxwell and F4 NormPair theorem surfaces
- `dc023ef31f72` Remove malformed CI theorem registration append
- `12940d9a1cc4` Repair theorem graph search registration
- `307096bf443b` Register README.md for new composed theorem surfaces
- `270fc2173585` Register .ci/actions_ci.dhall for new composed theorem surfaces
- `77736fc964f2` Register .ci/discovery/theorem_graph_search.m for new composed theorem surfaces
- `0f6eede9e266` Graph exact Maxwell prefix-regret extraction and F4 NormPair global conjugacy
- `a4617aaba312` Repair exact horizon regret field projection
- `7b096a2fd925` Complete F4 NormPair global conjugacy and Maxwell exact prefix regret extraction
- `0dab72aae78a` Remove non-existent Frank-Wolfe topology theorem from graph plan
- `38d09b1f3ffd` Keep Frank-Wolfe probability topology as explicit proof boundary
- `55930a30340f` Use actual e-graph closure and repair stationary composition premises
- `d5eb67e8a750` Graph F4 NormPair and Markov probability-topology boundaries
- `6f2c7072e0a2` Graph connected F4 NormPair and stationary boundary compositions
- `211777b5d520` Compose F4 NormPair stability and stationary boundaries
- `9f4fcc89e566` Extract Hodge-Maxwell GRU step through e-graph equality composition
- `5de3c254dc6b` Bind Hodge-Maxwell extraction to endogenous e-graph A* closure
- `add36ec315d0` Prune finite separation metadata and rebase graph on connected UAP
- `fdfa3238b4c4` Remove pruned finite theorem CI requirements
- `164626f3fde0` Prune disconnected finite theorem graph entries
- `deef493d6d82` Prune disconnected Fin and bounded finite theorem branches
- `0290772a4dd1` Repair Nat benchmark action arithmetic after Fin pruning
- `f0de66aa48fd` Remove remaining finite-index constructors from closed-loop benchmarks
- `6696e4385da2` remove Fin import
- `919e24f4d9a1` remove Fin import
- `ac932e17b749` remove Fin import
- `a299e295ee41` remove Fin imports
- `02edf39a5c7d` Register Hodge Maxwell F4 Watkins composition surface
- `3506f1f832d5` Register Hodge Maxwell F4 Watkins composition surface
- `8d02be108849` Register Hodge Maxwell F4 Watkins extraction graph
- `8210695f7be4` Fix learner-kernel parameter in Hodge F4 Watkins bridge
- `f051234a7bd6` Add fully connected Hodge-Maxwell GRU F4 Watkins e-graph extraction seam
- `8c49f2aefb71` Repair graph JSON delimiter after continuity theorem registration
- `f37e6e6757b8` Document Hodge-Maxwell continuity impossibility in theorem graph
- `8ebebb314e82` Document Hodge-Maxwell continuity and residual Fin boundary
- `d41506a7b43f` Complete graph edge for Hodge-Maxwell continuity impossibility
- `2dec7b68a6dc` Register Hodge-Maxwell GRU continuity impossibility in graph
- `663b02353b9b` Add connected Hodge-Maxwell discontinuity impossibility boundary
- `9362808d506c` Prune residual Fin action-domain remnants from canonical learner
- `0a589e5cbeb1` Record e-graph and A* as one semantic closure
- `615230bb4067` Bind e-graph equality composition to A* closure graph
- `831fbbf1439c` Bind e-graph equality composition to A* closure graph
- `e332251ae9c9` Bind e-graph equality composition to A* closure graph
- `713660ec7cfa` Bind e-graph equality composition to A* closure graph
- `658bd9b454ec` Connect e-graph equality composition to endogenous A* closure
- `73296b312a44` Fix discovery graph JSON after A* registration
- `cbe30c4c95f8` Register endogenous A* closure in discovery graph metadata
- `c64297a20e54` Document endogenous A* kernel closure
- `cf61e8f70f00` Graph emergent endogenous A* closure
- `0bb3e5f29c7c` Graph emergent endogenous A* closure
- `00672651e682` Graph emergent endogenous A* closure
- `6e79f0f55483` Add kernel-checked endogenous A* transport closure
- `4a7c87b65faa` Fix theorem graph numbering after transport promotion
- `b5262e93c257` Document carrier-polymorphic transport promotion
- `37ef275e3966` Remove promoted finite transport from pruned graph metadata
- `b4172e0bac91` Promote transport nodes in theorem relationship graph
- `58f74cb5b5aa` Update CI and discovery for generalized transport graph
- `c0a75c388e54` Update CI and discovery for generalized transport graph
- `9ef668b92b0b` Promote finite transport laws to carrier-polymorphic theorem graph
- `d801438c0679` Document adaptive sparsemax action-domain redesign
- `50f618dcd387` Make auto-merge method agnostic
- `02a40c5723e2` Refactor sparsemax onto adaptive Nat candidate lists
- `ebaebc1edb05` Provide gh in Nix shell for Dhall auto-merge
- `24ef97cc36dc` Define Dhall auto-merge lane for green PRs
- `78dc6177f207` Repair Maxwell equation conjunction syntax
- `a5549968cbc7` Repair Agda integer magnitude import for current stdlib
- `7b1a0b4f6ef8` Run auto-merge only after Agda and Mercury verification
- `1dc020a4949f` Add Dhall auto-merge lane for fully verified PRs
- `985553695198` Align README with carrier-polymorphic Maxwell graph
- `193f36e7971e` Prune stale Fin dependencies from Maxwell graph metadata
- `a10c522706e1` Fix graph audit wording
- `f2f8dd6791df` Compose Hodge-Maxwell non-injectivity boundary through collision impossibility
- `ee28e67c7aa3` Document Hodge-Maxwell injectivity boundary and carrier pruning
- `548c46059238` Remove residual finite-function dependency from Maxwell candidate paths
- `b18dca725488` Align Hodge-Maxwell closure with Z carrier and injectivity boundary
- `c21dc22f3740` Prune finite Maxwell graph dependencies and add injectivity boundary
- `2bd84d9edfc0` Register Hodge-Maxwell injectivity boundary in theorem graph search
- `bd61560393ca` Add connected Hodge-Maxwell global-injectivity impossibility boundary
- `9bcab1c593da` Repair stale nLab Maxwell/Tsallis graph boundary
- `daf7460858af` Repair Maxwell/Hodge-Maxwell graph after carrier-polymorphic promotion
- `652d92fa5ad2` Clarify continuous Maxwell existence boundary after finite-carrier pruning
- `0ea85119dae1` Restore connected F4 Frank-Wolfe theorem after Maxwell carrier pruning
- `97412234950e` Update graph audit for Maxwell/Hodge-Maxwell carrier retirement
- `1ff407d3541f` Record carrier-polymorphic continuous Maxwell/Hodge-Maxwell closure
- `a68df52f0057` Prune finite Maxwell candidate residue from theorem graph metadata
- `7c2870d7565b` Document carrier-polymorphic continuous Maxwell/Hodge-Maxwell boundary
- `92797aec3650` Update closure overlay for carrier-polymorphic Maxwell/Hodge graph
- `9e9f11f6d08f` Prune stale finite and retired theorem search plans
- `79330a917995` Update theorem graph search for carrier-polymorphic Maxwell/Hodge theorems
- `301d7a53bcda` Rewire Maxwell/Hodge graph to carrier-polymorphic continuous semantics
- `31843b0ed662` Prune finite Maxwell/Hodge carrier and generalize exact continuous composition
- `cdf5a29b7570` Normalize finite-carrier retirement wording in closure overlay
- `9d28b7b08f4b` Remove stale boundedness and fixed-carrier metadata
- `9b6c57de7363` Remove obsolete fixed-carrier wording from theorem prose
- `7b25e76f395b` Repair stationary subcomposition after observation pruning
- `3c1e26bba239` Remove retired observation entries from zero-dependency policy
- `444e1fcc3d6e` Align README with current stationary theorem name
- `03ab94e87659` Remove obsolete zero-dependency graph rows
- `d62d88aeff5e` Remove final fixed-carrier literal from Z audit
- `c85cda3c8fb6` Prune obsolete subcomposition rows from README
- `085780c02560` Synchronize CI ledger with current stationary theorem surface
- `c102640c77bf` Drop deleted boundedness subcomposition from graph search
- `b3e6ac1e5b44` Repair theorem graph search plans after observation pruning
- `a1da552bf931` Repair stationary theorem names after observation pruning
- `d7b54ccc3a4b` Supersede obsolete connected graph snapshot
- `dbd3788766b9` Supersede fixed-vocabulary closure note
- `933e116c1e18` Correct current Z audit after finite-carrier retirement
- `f25cedeb52ae` Prune stale candidate graph branches
- `aaca55be3f3d` Remove final fixed-carrier literal from README
- `b0fd736674ab` Update research note after fixed finite-carrier retirement
- `c54b28b1dfef` Update research note after fixed finite-carrier retirement
- `ca2e58439883` Update research note after fixed finite-carrier retirement
- `02575c3e2a52` Update research note after fixed finite-carrier retirement
- `1a4af29d5ad8` Refresh README for Z carrier and connected graph closure
- `8d7662ed4dae` Remove retired theorem names from CI ledger
- `0231d2cb72c6` Prune stale finite-observation graph surfaces
- `6488fde9811a` Remove retired Fin 256 observation graph plans
- `20ccd47eeb7f` Synchronize connected theorem closure after Fin 256 retirement
- `dc99a7ec6495` Retire Fin 256 from strict theorem graph
- `9b22ff217df8` Remove fixed Fin 256 payoffs from Matching Pennies
- `43f0bba97896` Retire Fin 256 theorem surfaces and generalize finite-state boundary
- `9a5d544b26e2` Retire Fin 256 token and observation machinery from canonical learner
- `ea17de3070e5` Make theorem graph cardinality gate self-maintaining
- `5a3eecfdb22b` Graph F4 global optimizer stability closure
- `21d4942b81e7` Repair Mercury graph output binding
- `24580073ccea` Repair Maxwell theorem constructor syntax
- `1a8fe72aa6c0` Repair exact Z subtraction syntax
- `d6d920e197bf` Repair q-log shell to use exact integer magnitude
- `a09b7bef5f51` Repair CI theorem ledger after finite-token pruning
- `95d7a2fe2459` Remove stale total token decode list from Z carrier
- `5cb534e34ea0` Synchronize graph with Z carrier and finite-token pruning
- `59c6d55a027d` Prune nonportable total-token isomorphism theorem
- `fb4d38e025fa` Prune impossible total Int8 token decode and retain finite-token encoding conjugacy
- `f210f444035f` Keep finite token alphabet explicit over exact Z carrier
- `5c4607c65a53` Update graph audit after bounded F4 repair
- `bd43df35b823` Classify repaired F4 promotion as transformative
- `575553109c9f` Repair F4 finite observation promotion without duplicate expansion
- `0dd3dc06c473` Record final carrier and graph closure audit
- `b021fc574afe` Document promoted Z optimizer and finite-observation closures
- `3709ff7cee20` Complete Z carrier graphing and promote optimizer stability
- `9eac3a15d767` Promote optimizer stability and left-inverse injectivity into connected boundaries
- `8e83348a270a` Prune duplicate theorem boundaries and make endogenous finite observations explicit
- `16c077399e8d` Separate F4 finite observations from exact Z optimizer algebra
- `d13cfb1202d6` Synchronize graph and research notes with finite-observation Int8 boundary
- `28fcadcab8e8` Synchronize graph and research notes with finite-observation Int8 boundary
- `8777951191b4` Synchronize graph and research notes with finite-observation Int8 boundary
- `967771946759` Synchronize graph and research notes with finite-observation Int8 boundary
- `5d6de92c3f2c` Repair finite-observation theorem types after Int8 carrier migration
- `1d30e6eccc2c` Reconnect finite pigeonhole boundaries through Fin 256 observations
- `8bdd76390862` Separate exact Int8 ring algebra from finite observations
- `c841377e93f7` Repair Hodge involution theorem parse boundary
- `bdb33aac0685` Repair exact Z arithmetic naming and roundtrip law
- `67bdcf74b3f1` Upgrade Agda Int8 carrier to unbounded Z
- `ff69636d42e6` Upgrade Agda Int8 carrier to unbounded Z
- `66bcaee49748` Align e-graph gate with Hodge-Tsallis-Walrasian bridge
- `0bd956de302a` Repair trailing strict graph node separator
- `003d758b7332` Repair escaped README paragraph break
- `3ceea4981ff0` Repair strict graph JSON node separator
- `702efd9ffdb3` Repair duplicate theorem graph completion declaration
- `c27c4d26bc18` Repair Hodge-Maxwell discretization certificate accessor
- `99992a9f6b09` Correct theorem declaration count after bridge
- `79f54b0c64ec` Normalize graph bridge diff without semantic cancellation
- `336a3419a6b8` Document connected Hodge-Tsallis Walrasian bridge
- `185f06c78131` Document connected Hodge-Tsallis Walrasian bridge
- `20b94e756ee1` Register Hodge-Tsallis Walrasian bridge in graph search
- `b3218210752a` Graph Hodge-Tsallis Walrasian projection bridge
- `4ea998f7b777` Add connected Hodge-Tsallis Walrasian projection bridge
- `4c9ec9dd3b42` Graph unbounded Int8 carrier boundary
- `20e2ac97c3a3` Document unbounded Int8 integer-ring boundary
- `0c968a8adb47` Repair integer Int8 roundtrip boundary
- `58712da24e11` Upgrade Equilibrium Int8 to unbounded integer algebra
- `9e2441e6ed95` Upgrade GameTheory Int8 to unbounded integer algebra
- `b9b0d00ea5c8` Record latest graph head and verification state
- `19d519590ff8` Correct idempotent conjugacy transport proof kernel
- `a83c9c573b55` Record finite-limit convex-duality and runtime audit continuation
- `76b38bf5068a` Document idempotent transport and finite-limit boundary
- `199b86583192` Align e-graph gate with idempotent transport theorem
- `d1b97858f2db` Graph hard-sign-style idempotent Hodge-Maxwell Tsallis transport
- `62c0fa6b38e3` Register finite idempotent Hodge-Maxwell Tsallis theorem
- `5a7ef5506863` Add finite hard-sign-style idempotent transport seam
- `56e61e787013` Export theorem graph completion predicate for e-graph sync
- `c860cb3d401a` Repair Hodge-Maxwell discretization accessor after field rename
- `ad73deeba7c9` Repair remaining discretization certificate reference
- `1ed7d6d132e7` Clarify Dhall analytic limits and record CI repair evidence
- `ffb69b29fe0c` Pregraph exotic analytic and equilibrium frontier candidates
- `808a20a13618` Repair Hodge-Maxwell discretization field syntax
- `5191563f3deb` Refresh theorem count and new closure tail
- `0d7950986e97` Document Maxwell impossibility and generalized equilibrium closures
- `53fce2d27e73` Sync Maxwell pigeonhole and Walrasian existence closures
- `0f2373cd8875` Update e-graph gate for Maxwell Walrasian closures
- `913c40cc4adb` Graph Maxwell pigeonhole and Walrasian existence closures
- `9fdd17a34f19` Add Maxwell finite-carrier impossibility and Walrasian existence closure
- `b9b1d809782e` Fix canonical theorem tail indexing
- `c0805b699632` Refresh theorem index and record-count boundary
- `c7c7a9349909` Document Tsallis involution Walrasian and runtime graph boundaries
- `726753747da1` Sync Tsallis Hodge involution and Walrasian graph boundaries
- `4b7a260e7bac` Update e-graph required theorem count after Hodge/Tsallis additions
- `d3eeeaaf01f5` Graph Hodge involution and Tsallis composition theorems
- `799e3fb922b9` Keep regular Walrasian frontier as graph metadata only
- `899450345b55` Add Hodge involution transport and Tsallis graph composition
- `0890e2f664d1` Close finite discretization and clarify remaining theorem frontiers
- `1e3e852a7cbe` Make discrete Hodge-Maxwell composition consume GRU field equations
- `323baaa27cdf` Document exact Hodge-Maxwell discretization and Tcl boundary
- `38a669f564b7` Graph exact finite Hodge-Maxwell discretization and classify recent transforms
- `e5e22948681f` Register exact finite Hodge-Maxwell graph layers
- `d9291bf911d1` Add exact finite Hodge-Maxwell discretization theorem layer
- `468c4cecf54c` Remove stale Maxwell candidate from connected graph
- `868186d0d856` Remove stale Maxwell candidate plan and use promoted theorem
- `5603d69db122` Align e-graph gate with promoted Hodge-Maxwell theorem
- `d93fe8c8afa7` Register exact finite Hodge-Maxwell theorem in dependency search
- `7dea0190f1ae` Promote exact finite Hodge-Maxwell graph theorem and QSA completion boundary
- `71061c3e9b51` Repair F4 regret monotonicity proof without changing semantics
- `d8a84e6b3b43` Promote finite continuous Hodge-Maxwell representation and regret monotonicity
- `ad1a00f4fdb5` Remove stale disconnected KKT wording from regret boundary
- `75de7cb1e9a5` Scrub stale disconnected optimizer and KKT nodes from graph metadata
- `cd98265dbf09` Finish removal of disconnected KKT theorem index entries
- `f328c2d8a421` Finish removal of disconnected KKT CI plan
- `4e582f9a1119` Document sole F4 horizon regret, QSA analytic boundary, and Maxwell PDE limit
- `2e0742af28f9` Align e-graph gate after optimizer and KKT pruning
- `dfa4e0eb59fd` Require only the connected F4 horizon-regret optimizer endpoint
- `900ad19cf0fe` Collapse strict graph to sole F4 optimizer and formalize Maxwell/QSA boundaries
- `9d9735ce115d` Prune standalone KKT theorem surfaces with no retained dependency
- `db7d9cfa59ee` Collapse optimizer boundary to F4 and make cumulative regret explicitly horizon indexed
- `46d1f6d3cb7d` Refresh transformative commit ledger and remove stale F4 KKT candidate dependency
- `d25813b51cf9` Clarify optimizer pruning boundary comment
- `81a41dcb8fec` Align e-graph gate with complete theorem plan count
- `6505174ed0fc` Restore Maxwell/Tsallis finite exact conjugacy theorem surface after optimizer pruning
- `ff0fa123a88a` Document horizon-indexed regret boundary and optimizer pruning
- `efed37d4985d` Update e-graph required theorem count after endpoint pruning
- `da085be81a91` Align Mercury graph search with connected horizon-regret consumers
- `5beecaf6b2d9` Prune disconnected optimizer endpoints and graph horizon-regret consumers
- `5944bb75b4d0` Prune standalone optimizer/KKT surfaces and make regret bounds horizon-indexed
- `0b92aeda10f4` Automate custom and Frank-Wolfe rounding regret graph plans
- `4d0baa6a7070` Promote custom optimizer and Frank-Wolfe regret compositions
- `8e0ed34c4b92` Add custom optimizer and Frank-Wolfe rounding regret seams
- `9827ac531e09` Document corrected optimizer boundary and Maxwell Tsallis theorem
- `1604c9187e3e` Update e-graph gate for Maxwell exact composition plan
- `422f2952e55b` Remove Lion plan and keep Maxwell composition automated
- `bc067ba0b66f` Register automated Maxwell Tsallis exact conjugacy graph plan
- `47cb525b9057` Make Tsallis divergence transport nontrivial
- `22bec3a08db9` Add Maxwell Tsallis finite exact conjugacy theorem surface
- `9e77c7bf6c1c` Refine custom optimizer boundary and pregraph Maxwell Tsallis exact composition
- `041f1ba78957` Close graph audit and theorem-boundary ambiguities
- `f283dbd779b7` Prune unused Tcl dev-shell dependency
- `efeb8319d115` Fix Mercury implementation redeclarations
- `018f58815feb` Fix duplicate Agda constructor/value binding
- `c17527dd87b3` Place restored graph plan definitions in implementation section
- `9459f25c28a6` Qualify two-counter machine halting field
- `1a4c9f15a347` Restore theorem graph plan predicates required by e-graph CI
- `d650c23359da` Document automated graphing and Maxwell promotion boundary
- `8e0e654cc117` Sync e-graph required plan count with automated theorem graph
- `d240a500fe5a` Automate graph plan for fully connected F4 Frank-Wolfe theorem
- `255c2e736717` Graph fully connected F4 Frank-Wolfe optimizer seam
- `08572d86e8d3` Promote F4 Frank-Wolfe into connected optimizer composition
- `62535a8532ee` Correct optimizer seam to F4 Frank-Wolfe and constrain Maxwell scope
- `ee2d8b29e7d6` Require F4 Frank-Wolfe and Maxwell candidate graph nodes
- `d0e8420397af` Expose F4 Frank-Wolfe and Maxwell graph plans
- `4a5d7286024b` Pregraph F4 Frank-Wolfe and Maxwell-only finite representation
- `111219337865` Keep Maxwell representation as graph candidate only
- `795c57900db9` Add connected F4 Frank-Wolfe theorem boundary
- `04d1c87c56f9` Record Lion graph transformation provenance
- `caa775ba2c27` Make Lion and connected regret theorems required graph nodes
- `203e4844919e` Register connected Lion theorem in composition graph
- `7e12118db745` Derive Lion connected bound from existing optimizer theorem
- `4f150f1c892b` Add connected Lion regret theorem surface
- `c296f76446ab` Compose Lion descent term into regret bound proof
- `0c8c7c255f73` Add Lion descent and KKT research to regret boundary
- `71c03daed04f` Expose connected Lion regret graph plan
- `4684de81c37f` Pregraph connected Lion descent/KKT regret boundary
- `83d03e03915c` Remove unused Lion theorem surface and keep connected residual only
- `380257e40d78` Connect Lion descent/KKT term to optimizer regret boundary
- `f7cd36b4cc22` Document connected Jensen minimax regret boundary
- `ab9703f619ff` Expose connected optimizer regret graph search plan
- `672a443c687c` Graph connected Jensen minimax regret optimizer theorem
- `8732f2af8780` Repair connected KKT parameter witness
- `4b76a764db82` Add connected Jensen minimax rounding KKT Markov theorem surface
- `414cbeba22f2` Make logarithmic scan certificate semantically explicit
- `206efe860552` Repair resumed graph-search duplicate Mercury declarations
- `7dc0b5f27630` Repair scan theorem scope and forbidden-token gate
- `85f4d6c4b1f0` Document parallel scan complexity boundary
- `f36cd3a4bc05` Pregraph logarithmic SIMD scan boundary
- `dde563000ff8` Graph parallel prefix complexity theorem surfaces
- `e360039221ba` Correct parallel scan complexity theorem boundary
- `5f6f39e829a1` Add conditional parallel prefix complexity theorem
- `c40c418a88af` Fix flake formatting after Tcl runtime swap
- `0a58f9b32e47` Replace Scheme and Raku CI runtime packages with Tcl
- `24d4cd786e82` Clarify connected RNN computability boundary
- `1be20618b2ac` Document graph resumption and emergent theorem audit
- `ab76cd457b19` Complete emergent theorem and future graph contract
- `36e7d43d8a2c` Export all graph-plan predicates consumed by e-graph sync
- `f90d769a4898` Repair finite-state separation proof against Agda 2.8 API
- `e5971a299554` Align strict separation record universes
- `c5ea7faa9d9d` Update README with strict separation completion
- `1e75c039ccd8` Document literature-aligned strict separation construction
- `daecbf9b5ce6` Record completed literature-aligned separation surface
- `0a9ea528475b` Add literature-aligned strict recurrent separation theorem
- `b0c607f68a0a` Bind exotic neural separation candidates to proof gates
- `d6b80d9c6551` Document strict separation contract
- `e0b97e05dbb8` Add strict neural separation proof contracts
- `c3445ecba8b5` Record proved endogenous closure and verification boundary
- `794ccf87e263` Mark endogenous closure as proved on Agda surface
- `1d33f7991606` Prove endogenous RNN-LM vocabulary observation closure
- `c5368145a527` Document promoted endogenous closure theorem
- `991314c4b063` Promote endogenous vocabulary observation theorem
- `48a30ded3bda` Graph promoted endogenous RNN-LM closure
- `d815401d7577` Promote endogenous RNN-LM vocabulary observation closure
- `7c9862b81d66` Document Int8 vocabulary and recurrent closure boundary
- `63f61d011f0e` Add finite-vocabulary recurrent closure candidate
- `19f96747730e` Add pregraphed endogenous theorem closure overlay
- `0d5151958a48` Document complete connected theorem graph closure
- `3dece4065ed0` Repair endogenous graph search string import
- `2e67442f438a` Repair recurrent scan input lookup compatibility
- `7ce23960a9c9` Repair graph plan implementations below Mercury implementation
- `dcfdde047e27` Add algebraic proof of nonlinear sequence storage generation
- `cf53715b3c15` Document GRU automata graph research boundary
- `def9ee9551fd` Pregraph automata sign optimizer affine candidate
- `79ca8abfadd3` Repair missing graph plan implementations
- `bfb19ad436c9` Repair Agda finite-factor recurrence helper
- `1c7789639b42` Fix Mercury theorem graph predicate placement
- `1ca9b5b0d94a` Document learner replacement quotient candidate
- `6f74b4f7e8b4` Graph learner replacement quotient endogenous candidate
- `56d499768e4d` Document nonautomata sign optimizer affine candidate
- `142a1b8816bf` Graph nonautomata non-tropical sign optimizer affine candidate
- `d3d7416fe254` Document non-tropical sign optimizer affine connected candidate
- `6425380dd41f` Graph non-tropical sign optimizer affine connected candidate
- `11c371b1dc91` Document sign optimizer affine connected candidate
- `1fc4a76777c9` Refine sign optimizer affine connected theorem candidate
- `36f96e1efb58` Document unified tropical topology neighborhood conjugacy candidate
- `06e7fc3c4db4` Graph tropical HardSign topology neighborhood conjugacy candidate
- `2ce8e87b7660` Document tropical HardSign quotient and zero-dependency graph policy
- `b7f3ce251b8e` Extend connected theorem graph with tropical HardSign quotient candidate
- `87078fdb6b35` Document finite-factor automaton and tropical quotient graph
- `eff80d5bc163` Graph finite factor automaton closure and tropical quotient candidate
- `8b9a775dce85` Document internal Nix Dhall verification authority
- `f8a3826d7016` Promote pre-graphed automata and HardSign seams into connected graph
- `d53313518cf4` Record internal verification boundary and emergent hard-sign automaton candidate
- `602279b84578` Document strict full-connected separation proof obligations
- `554844b68144` Complete strict separation witness and future-theorem graph contract
- `6e7d3150129e` Document full connected separation graph and recurrence regularization seam
- `cd9a2bace222` Promote disconnected components into full connected separation graph
- `81c3d1ce2e26` Complete connected strict neural separation graph
- `63d518a56dfd` Document strict neural function-class separation criterion
- `6359f6c2b8f9` Add strict neural function-class separation graph
- `a91101e2ab10` Prune non-README Markdown
- `d1b67eca3b10` Repair stale stationary theorem documentation
- `4b347ec6537b` Gate composite graph plans on dependency validity
- `77c0ac1360d2` Repair graph-search generated-plan validation gate
- `fd863ba7302c` Resync theorem branches after README updater repair
- `911b394387ec` Require exact README commit totality
- `e017e78d483e` Require exact README commit totality
- `5a54c90db92f` Sync theorem branches without rewriting history
- `98b26cce7a0a` Document slow README commit totality
- `23315d86ad75` Schedule slow README commit totality
- `871cc86697f4` Add Dhall README totality updater
- `0a40fb898136` Add slow README Nix app
- `22cc1f922e1b` Document slow README commit totality
- `7b0eb26af443` Schedule slow README commit totality
- `fd67fdac563a` Add Dhall README totality updater
- `20998f11c02e` Add slow README Nix app
- `42b27cd4a84b` Gate endogenous RNN-LM POMDP topology closure
- `e0d636e8c5e6` Pre-graph endogenous RNN-LM POMDP topology closure
- `8a9ad5f649ff` Gate endogenous RNN-LM POMDP topology closure
- `b5f422d64880` Pre-graph endogenous RNN-LM POMDP topology closure
- `13cb2f657ee9` Require exhaustive canonical record graph
- `d332c8f80a49` Pre-graph all canonical Agda record declarations
- `8df5b1a832bf` Prune README and document complete Agda record graph
- `ae12e870b3ae` Prune README and document complete Agda record graph
- `15eff5584b78` Require exhaustive canonical record graph
- `ee3c3f4ca38f` Pre-graph all canonical Agda record declarations
- `d27ab4607254` Rewrite theorem graph README
- `abf8d300658b` Sync theorem graph gate count
- `c63953533caa` Pre-graph complete theorem monolith
- `2cc27fcb40cf` Declare emergent endogenous theorem in CI
- `5826ab13b770` Update e-graph theorem gate count
- `6973472c4b50` Clarify language roles and theorem graph in README
- `067ad019aba6` Pre-graph emergent endogenous RNN-LM POMDP closure
- `1b708165ada0` Add emergent endogenous RNN-LM POMDP closure
- `a9962b262815` Consolidate theorem graph, RNN-LM boundaries, and monograph
<!-- END RECENT COMMIT TOTALITY -->
