# Actions — canonical learner, theorem, and economic dependency topology

This repository is a mechanically checked study of one coupled recurrent learner and the exact consequences that follow from its definitions. The authoritative mathematical surface is Agda; the discovery and CI layers are subordinate tooling.

The current thesis-facing claim is deliberately narrow: the formalization makes the dependency boundary explicit. Exact learner dynamics yield exact representation, quotient, factorization, and stability facts. They do not, by themselves, yield convergence, a fixed point, market clearing, supporting prices, or Walrasian equilibrium existence.

## Authoritative sources

- `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda` — canonical learner definitions and definitional laws.
- `Exotic/ERL/FullCoupled/TheoremsMonolith.agda` — theorem consumer and semantic/economic boundary.
- `.ci/actions_ci.dhall` — verification lanes and required checks.
- `.ci/discovery/` — declaration extraction, dependency discovery, and graph consistency checks.
- `docs/research/theorem-improvement-completion-2026-09-26.md` — completed theorem-improvement search and proof-boundary note.
- `docs/economics/` — production/equilibrium vocabulary and economic boundary documentation.

The Agda monoliths are intentionally kept as the proof source. Graphs are explanatory and discovery artifacts; a graph edge never substitutes for an Agda proof.

## Repository-wide semantic e-graph closure

All surviving Agda modules are covered by the same proof-only semantic transport boundary inside `TheoremsMonolith.agda`: the theorem monolith contains the indexed semantic family, e-graph transport, certified rewrites, and typed A* cost/heuristic model. The A* cost guides traversal; it never becomes evidence for equality. The learner-side A* seam remains in `TheoremsMonolith.agda` as `CanonicalAStarCostGuidanceTheorem` and `CanonicalEndogenousEGraphAStarTransportClosureTheorem`.

This is the repository's **full unconditional semantic e-graphed closure**: unconditional over every supplied indexed Agda semantic family, every module in that family, and every sound path. It is not an unconditional claim that every physical or economic theorem is inhabited. In particular, it does not manufacture Maxwell Law-I/Law-III witnesses, equilibrium witnesses, or other domain-specific semantic inhabitants.

The current Agda inventory is intentionally minimal:
- CanonicalLearnerMonolith.agda — canonical learner definitions and definitional laws.
- TheoremsMonolith.agda — the sole theorem/semantic monolith, including the inlined statistical, physics, economics, fractal, limit, e-graph, A*, and counterexample contracts.


The monoliths remain the proof authority. Auxiliary Agda files are not independent theorem authorities; their semantics enter the common transport layer through explicit typed terms.

### Complete surviving-Agda closure index

The repository-wide semantic closure is indexed by exactly the two surviving Agda files in Exotic/ERL/FullCoupled: CanonicalLearnerMonolith.agda and TheoremsMonolith.agda. The theorem monolith's RepositoryAgdaModule enumeration is the live source of truth for that two-file proof surface.

The exact chain is:

    two surviving Agda monoliths
      -> supplied sound interpretation
      -> sound e-graph path
      -> A*-guided traversal
      -> exact semantic endpoint equality

TheoremsMonolith.agda remains the sole theorem authority; graphs, discovery output, and historical notes are subordinate artifacts.

## Source-grounded Maxwell semantic boundary

The Maxwell semantic adapters are aligned with the external mathematical semantics rather than treating search artifacts as proofs. nLab's Noether treatment connects variational symmetries with on-shell conserved currents; its conserved-current entry defines horizontal closure on the dynamical shell. nLab's Maxwell and Hodge-Maxwell entries provide the differential-form equations and the Hodge-theoretic existence/uniqueness statement under its stated hypotheses. nLab's action-functional and Euler-Lagrange entries connect action critical loci with equations of motion, including Maxwell's equations.

The Stanford Encyclopedia of Philosophy's gauge-theory entry independently records the modern Maxwell variables, current conservation, the Lagrangian/Euler-Lagrange route to Maxwell's equations, and the Noether correspondence between classical Lagrangian symmetries and conserved currents. Wikipedia supplies accessible cross-checks for Maxwell charge conservation, Euler-Lagrange field equations, and the electromagnetic tensor/Lagrangian formulation. The Tsallis source surface describes Tsallis entropy as a one-parameter generalization of Boltzmann-Gibbs-Shannon entropy and emphasizes nonadditivity; Wikipedia documents the q-statistical construction and its q-logarithm/q-exponential relations.

These sources justify the semantic shape of the adapters. They do not provide the repository-specific discrete current-preservation equality, learner↔Maxwell inverse, or learner-step conjugacy. Those remain explicit typed obligations in NLabMaxwellSemanticClosure; no external source is imported as an Agda axiom.

The maintained primary-source audit is docs/research/four-law-primary-source-closure-audit-2026-09-25.md. The focused ZPF/ω³ implementation note is docs/research/zpf-omega3-gru-statistical-law-2026-09-25.md.

<!-- BEGIN GENERATED DOCUMENTATION INDEX -->

Generated from the tracked Markdown surface: 40 files.
The root README is the GitHub-facing entry point; detailed evidence remains in the linked source documents. Internal CI/discovery notes and historical agent plans are intentionally excluded from this public documentation index.

### Economics

- [Economic e-graph: emergent-only Arrow–Debreu](docs/economics/economic-egraph-emergent-arrow-debreu.md)
- [Economic A*-E-Graph Target: No Primitive Economic Price](docs/economics/economic-egraph-no-primitive-price.md)

### Research

- [Adaptive sparsemax action-domain redesign — 2026-09-23](docs/research/adaptive-sparsemax-action-domain-2026-09-23.md)
- [Canonical Integer-GRU global left-inverse and conjugacy closure — 2026-09-26](docs/research/canonical-integer-gru-global-left-inverse-2026-09-26.md)
- [Carrier-polymorphic frontier closure — 2026-09-26](docs/research/carrier-polymorphic-frontier-2026-09-26.md)
- [Complete connected theorem graph closure — 2026-09-22](docs/research/complete-connected-theorem-graph-2026-09-22.md)
- [E-Graph / A* convergence closure — 2026-09-27](docs/research/egraph-astar-convergence-2026-09-27.md)
- [E-graph frontier: MARL physics ↔ generalized Walrasian convergence and injectivity — 2026-09-28](docs/research/egraph-marl-walrasian-convergence-injectivity-2026-09-28.md)
- [Expanded generalized aggregate excess demand e-graph — 2026-09-28](docs/research/egraph-expanded-aggregate-excess-demand-2026-09-28.md)
- [Endogenous A* kernel-checked closure — 2026-09-23](docs/research/endogenous-astar-kernel-closure-2026-09-23.md)
- [2026-09-23 finite-carrier transport promotion](docs/research/finite-carrier-transport-promotion-2026-09-23.md)
- [Four-law primary-source closure audit — 2026-09-25](docs/research/four-law-primary-source-closure-audit-2026-09-25.md)
- [General-purpose workload and GUI boundary — 2026-09-27](docs/research/general-purpose-workload-gui-boundary-2026-09-27.md)
- [Graph closure audit — 2026-09-23](docs/research/graph-closure-audit-2026-09-23.md)
- [GRU automata/sign-optimizer graph research](docs/research/gru-automata-signoptimizer-graph.md)
- [Arbitrary-limit GRU fractal closure and e-graph/A* composition — 2026-09-26](docs/research/gru-fractal-arbitrary-limit-closure-2026-09-26.md)
- [GRU fractal domain adapters — 2026-09-26](docs/research/gru-fractal-domain-adapters-2026-09-26.md)
- [GRU-injective fractal composition — 2026-09-26](docs/research/gru-fractal-injective-composition-2026-09-26.md)
- [GRU fractal limit convergence adapter — 2026-09-26](docs/research/gru-fractal-limit-convergence-adapter-2026-09-26.md)
- [Unbounded Int8 integee-eing upgeade — 2026-09-23](docs/research/int8-unbounded-z-ring-2026-09-23.md)
- [Int8 vocabulary boundary and recurrent closure — 2026-09-22](docs/research/int8-vocabulary-recurrent-closure-2026-09-22.md)
- [Integer LayerNorm stability and growth — 2026-09-27](docs/research/integer-layernorm-stability-growth-2026-09-27.md)
- [F4 horizon-indexed rounding-bias residual regret boundary](docs/research/jensen-minimax-rounding-kkt-markov-bound.md)
- [CI artifact format decision — JSON to Dhall — 2026-09-27](docs/research/json-to-dhall-ci-2026-09-27.md)
- [Law IV carrier-polymorphic Tsallis audit — 2026-09-25](docs/research/law-iv-tsallis-carrier-polymorphic-2026-09-25.md)
- [Learner equivalence class: algebraic and computational boundary](docs/research/learner-equivalence-class.md)
- [MARL-facing laws, Hodge-Maxwell composition, and the F4 growth ray](docs/research/marl-laws-hodge-maxwell-f4-ray-2026-09-25.md)
- [Algebraic proof: nonlinear sequence storage and generation](docs/research/nonlinear-sequence-storage-generation-algebra.md)
- [Real semantic e-graph and staleness policy — 2026-09-26](docs/research/real-semantic-egraph-staleness-prune-2026-09-26.md)
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
        +--> F4 optimizer stability and exact recurrent composition
        |
        +--> F4 optimizer stability
        |          |
        |          +--> exact unit-forcing growth ray
        |          +--> no unconditional infinite-horizon F4 upper bound
        |
        v
F4 optimizer stability theorem
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

The canonical learner state contains the recurrent learner channels, optimizer state, counts, and q-log state. Its `Int8` name is an unbounded `ℤ` wrapper in the current definition; it is not a `Fin n` carrier. Integer LayerNorm is represented by exact integer centering/radicand arithmetic plus an explicit non-zero square-root certificate; the normalized output is an exact integer ratio with integer scale, gamma, and beta. The LayerNorm branch now also has explicit configuration-stability and epsilon-radicand linear-ray theorem surfaces, separate from the F4 optimizer-state growth ray. The E-Graph/A* plan layer packages list concatenation as an Agda Monoid; that monoid describes candidate-plan composition, not semantic equality.

The current closed facts include:

- the canonical LCB `totalCount` increments exactly once per canonical step;
- every positive iterate strictly increases that count, hence there is no nontrivial finite cycle of the full canonical state;
- the policy is invariant under optimizer replacement;
- `CanonicalF4GlobalOptimizerStabilityTheorem` is closed;
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

The graph evidence stack is intentionally minimal: Dhall is the machine-readable evidence/interchange layer; Mercury supplies dependency discovery and semantic graph processing. TSV and CSV are not canonical topology formats. The concrete integer LayerNorm rewrite surface is attached to the existing sound E-Graph-A* closure; A* costs guide traversal and never become equality evidence. SQLite or NoSQL is not warranted for the current deterministic, repository-local dependency workload; add a database only if a demonstrated query/history workload exceeds what the JSON evidence and normal shell tooling can do. Tracked and generated CI reports are Dhall; JSON is not a canonical CI artifact format.

The orchestration arrows are not mathematical implication arrows.


## General-purpose workload and GUI boundary — 2026-09-27

The semantic boundary is now intentionally independent of the implementation language used by a future general-purpose workload.

The repository layers are:
- Agda with `--safe`: the only semantic and proof authority.
- Mercury: declaration extraction, dependency discovery, and semantic graph processing.
- Dhall: the typed verification/evidence contract.
- Nix: the reproducible build/development environment and host composition.
- Workload implementations: replaceable native or embedded languages; they consume explicit interfaces and never become a second semantic authority.

A workload may therefore use Go, Nim, Lua, Chibi Scheme, Roc, Swift, Tcl/Tk, or another language when a concrete workload needs it; this prompt adds only Tcl/Tk as the concrete native GUI path. The candidate list is non-exhaustive and does not make every language a repository dependency. The CI surface must not reject a language merely because it was absent from an earlier phase. What remains prohibited is duplicated semantic authority: an implementation language must not introduce a parallel theorem model or an alternative canonical definition of the learner.

For desktop Linux targets, Tk remains an optional native GUI adapter. WebAssembly is a separate presentation target, not the canonical desktop runtime. A browser/WASM build can expose the same workload contract through a browser host, while microOS/Aeon, NixOS, VanillaOS, and similar Linux systems can use a native GUI adapter without acquiring a browser dependency.

Tk itself should therefore not be redefined as “Tk in WebAssembly”. The browser adapter should be treated as a separate host boundary. Existing browser-oriented Tk-compatible projects implement their widgets through JavaScript/HTML rather than becoming the Tk desktop implementation; a direct Tk/WASM path would require its own platform port. See [Tk](https://github.com/tcltk/tk), [Emscripten WebAssembly](https://emscripten.org/docs/compiling/WebAssembly.html), and [wTk](https://core.tcl-lang.org/wtk/home).

Guix is not a repository requirement. Mermaid is not a graph or CI requirement. Neither is needed by the semantic core.

For this prompt only, the concrete native GUI adapter is `workloads/tcltk/native_tk_adapter.tcl`. It is presentation-only: it accepts an external `ACTIONS_WORKLOAD_LABEL` value and renders it with Tk; it does not define learner semantics or CI evidence.

## MARL, Hodge-Maxwell, and optimizer semantics

The repository now promotes one closed MARL-facing composition: `CanonicalMARLLawCompositionTheorem`. It packages the recurrent-prefix law, the exact F4 step law, the endogenous Watkins target law, and the already-closed `CanonicalGRUF4WatkinsPrefixCompositionTheorem`.

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
last-processed-commit: 727b033d9cc1e363e130629f764cafa716078707
unprocessed-commit-count: 11

The scheduled updater accounts for every commit since the previous processed commit.
ascii-safe-commit-subjects: true

- `727b033d9cc1` docs: index economic e-graph composition
- `ac3524335f5c` docs: record economic e-graph composition seam
- `6990eb4c6d60` ci: gate economic e-graph composition
- `c1b8d368786d` fix: tighten economic e-graph composition theorem
- `3d1d9829923c` feat: compose economic e-graph witness algebra
- `5a89b4b9528f` docs: index MARL Walrasian e-graph frontier
- `b302d796762a` docs: graph MARL Walrasian convergence injectivity frontier
- `af05810f1994` ci: gate certified e-graph path composition
- `e1b03fe0e8b9` docs: record certified e-graph path composition
- `3546a848b5e3` feat: compose certified e-graph paths
- `f82e84d74736` docs: refresh README from commit totality
<!-- END RECENT COMMIT TOTALITY -->


## Current economic e-graph closure

The generalized aggregate-excess-demand e-graph is now explicit in `TheoremsMonolith.agda`. Its typed chain covers individual demand, firm supply, aggregation, excess demand, regularity (continuity, degree-zero homogeneity, and Walras law), aggregate feasibility, market clearing, supporting prices, and equilibrium characterization.

The unconditional stationary-price seam is also in the theorem monolith. `canonicalStationaryPriceUpdate` is the canonical zero-step operator `p ↦ p`, `canonicalStationaryPriceLaw` proves stationarity by `refl`, and `UnconditionalEGraphEconomicStationaryPriceComposition` transports that law alongside a certified semantic e-graph path. This removes an externally supplied `Price → Price` operator from the unconditional stationarity core while preserving the distinction between identity stationarity and a substantive excess-demand price-adjustment process.

The repository does **not** infer a nontrivial price-adjustment law, an excess-demand root, supporting-price existence, Walrasian existence, uniqueness, stability, or convergence merely from these carriers. Those require corresponding mathematical witnesses or additional structure. The e-graph records those boundaries rather than treating them as proofs.

The Agda proof authority remains exactly two files: `CanonicalLearnerMonolith.agda` and `TheoremsMonolith.agda`. Auxiliary documentation and discovery artifacts are subordinate to that authority.
