# Actions

This repository keeps one canonical semantic learner, one canonical theorem monolith, Mercury-only semantic e-graph discovery, and a pinned Nix-connected proof pipeline.

## Canonical proof surface

The learner source is:

`Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

The only active theorem source is:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

That theorem monolith imports the learner monolith as its only repository-local semantic source and is checked with `{-# OPTIONS --safe #-}`.

There is no generated Agda theorem projection. Mercury synchronizes only against the source-derived theorem monolith; Nix supplies the package environment, the NixOS-maintained installer action bootstraps Nix, and Agda performs the kernel check. One theorem source, because apparently software projects require ritual before they will stop duplicating themselves.

## Which tool owns the sync?

**Mercury owns e-graph sync and semantic discovery. Nix owns toolchain bootstrap and reproducible execution. Agda owns proof acceptance.**

The division is deliberately strict:

`CanonicalLearnerMonolith.agda` + `TheoremsMonolith.agda`
-> Roc typed-functional CI orchestration
-> Mercury source-derived in-memory semantic law extraction
-> Mercury A* cost-guided dependency search
-> Mercury e-graph normalization
-> Mercury theorem-monolith sync gate
-> Nix-pinned `agda --safe`
-> kernel-checked theorem monolith

Mercury never writes a second Agda theorem file. The sync program is:

`.ci/discovery/theorem_monolith_egraph_sync.m`

The generic e-graph implementation remains:

`.ci/discovery/interpolated_theorem_egraph.m`

The e-graph is a discovery/proof-plan normalization layer, not a second proof authority.

## Nix toolchain strategy

CI installs Nix once and enters the repository flake. The flake pins nixpkgs at the repository revision and supplies the upstream Agda setup, Mercury 22.01.9, and Roc. Roc is the only repository-side CI program source: `.ci/actions_ci.roc` is a typed functional executable source, while Nix remains the declarative environment/build layer.

The Roc program invokes Agda `--safe`, Mercury, theorem-only A* graph search, e-graph saturation, the semantic contract, and the canonical source audit directly as processes. It does not invoke a shell interpreter, Node, Python, Lua, or a JavaScript runtime.

Roc is used specifically for its pure functional model, explicit effects, native execution, and documented terminal-command and CI-script examples. The exact pinned nixpkgs revision already contains the Roc compiler used by the Linux CI runner.

## Typed functional CI scripting and A* e-graph discovery

The repository does not treat “general-purpose language” as sufficient for CI scripting. The replacement criterion is the intersection of typed functional semantics, explicit effects/process execution, native Linux execution, and an installable upstream compiler in the pinned Nixpkgs revision.

Roc matches the actual CI job: it is a pure functional language with explicit effects, documented terminal-command execution, and documented real-world CI scripts. The CI runtime therefore stays native and statically typed without introducing a JavaScript or Lua execution layer.

The executable path is:

`.ci/actions_ci.roc`
-> Roc process execution
-> Agda / Mercury binaries
-> theorem-source extraction
-> A* dependency frontier
-> e-graph saturation
-> cost-guided extraction
-> `theorem-monolith-egraph-sync.json`

A* is a graph-search cost policy, not a proof authority. Agda `--safe` accepts proofs; Mercury derives the theorem dependency graph and equality-saturation plan; Roc only orchestrates those existing authorities.

## Infinite-state proof

The infinite-state argument is in the theorem monolith under:

`canonicalInfiniteStateOrbitEmbedding`

It proves the Nat-indexed canonical orbit is injective:

`C.iterateCanonical K m s ≡ C.iterateCanonical K n s -> m ≡ n`

The proof is constructive. It uses the exact clock-growth law

`C.clock (C.iterateCanonical K n s) ≡ C.clock s + n`

and Nat cancellation. There is also the no-global-exact-UAP route:

`canonicalPigeonholeNatClockContradiction`

and:

`canonicalNoGlobalInt8DiscreteUAPOnOrbit`

Those together make the boundary explicit: the canonical orbit is infinite in the Nat-indexed sense, while a single finite `Int8` observation cannot admit a global exact left inverse over that orbit.

## Exact bounded universal approximation through continuous left-injectivity

The strict theorem surface does not smuggle in a topology library. Continuity is an explicit predicate in:

`ContinuousLeftInverseTheorem State Feature observe inverse Continuous`

That witness supplies:

- continuous observation;
- continuous inverse;
- an exact left inverse;
- injectivity of the observation;
- exact readout transfer for arbitrary targets.

The finite exact-UAP consequence is:

`boundedUniversalExactApproximation-through-continuousLeftInverse`

Its domain is `Fin bound`. For every target `State -> Output` and every bounded index, the theorem gives exact equality:

`target (embed i) ≡ target (inverse (observe (embed i)))`

The underlying record is:

`BoundedContinuousLeftInverseExactApproximationTheorem`

and the implementation route is:

`boundedExactApproximation-on-boundedOrbit`

So this is an exact bounded universal readout theorem through a continuous left inverse, not a fabricated metric approximation theorem.

## Connected composed Agda theorem

The main composed theorem is:

`canonical-endogenous-minimax-bellman-shapley-uap-theorem`

It combines:

- exact biased Watkins, negative q-Munchausen, and F4-L2 target semantics;
- an explicitly supplied minimax/Bellman-Shapley inclusion class;
- endogenous left-inverse factorization;
- exact discrete UAP from a left inverse;
- exact recurrent scan semantics for the endogenous target stream;
- continuous-left-inverse readout transfer;
- **bounded exact universal approximation/readout from that continuous left inverse**;
- ring-state injectivity;
- the explicit **infinite-state orbit embedding**;
- orbit-observation separation as an explicit contract;
- the Nat-clock pigeonhole contradiction;
- impossibility of a global exact `Int8` UAP over the unbounded canonical orbit.

The constructor for the composed theorem directly includes the bounded theorem and infinite-state orbit proof, so the Mercury dependency graph can see those as connected source laws rather than decorative documentation. The minimal exact-universal-readout certificate exposes three facts directly: a continuous left inverse, explicit observation separation, and exact readout for every target. Separation is derived from the left-inverse witness, so the separated field is intentionally redundant but makes the proof contract visible.

## Mercury e-graph sync contract

The discovery target is not fixed; every non-reflexive source law is a seed, and dependency expansion continues until each maximal simple dependency chain is reached:

`TheoremsMonolith.agda#canonical-endogenous-minimax-bellman-shapley-uap-theorem`

The Mercury sync gate requires only that source-derived laws and emergent composition plans are nonempty, structurally valid, and successfully inserted, saturated, analyzed, and extracted. No theorem name, dependency list, candidate-count cap, or symbolic target is hard-coded.

The sync report records:

`single_agda_source = true`

`generated_agda_module = false`

`proof_authority = Agda --safe`

Agda is still the only component allowed to accept the theorem. Mercury can discover that the wires are connected; it cannot bless a bad proof. Civilization narrowly avoids another parser being mistaken for a kernel.

## Graph-derived emergent hypotheses

The former unigram, bigram, and onion items were empirical representation hypotheses. They are removed from the canonical README claim surface because they were not source-derived Agda laws and were not outputs of the Mercury theorem graph.

This pass adds **exactly two new theorem hypotheses** to the graph-facing surface:

1. **Integer Haar scaled orthogonality** — `canonical-integer-haar-scaled-orthogonality-theorem`. Its source dependencies are exactly `canonicalIntegerHaarCross` and `canonicalIntegerHaarEnergy`: the two-point integer/scaled Haar kernel has zero cross-term and exact energy 2. This is deliberately not the normalized real Haar matrix; `1/sqrt(2)` is outside the canonical `Int8` carrier.

2. **A* cost guidance** — `canonical-a-star-cost-guidance-theorem`. Its source dependencies are exactly `canonicalAStarZeroCost`, `canonicalAStarSuccessorCost`, and `canonicalTokenLogitTrace-append`: the graph-search cost identities compose with the exact causal token-trace split law.

Mercury owns the discovery path: it extracts declarations from `TheoremsMonolith.agda`, follows identifier-derived dependency edges, orders maximal paths with its A* score, inserts the source laws and graph plans into the e-graph, saturates, analyzes, and extracts. The theorem names above are not a hard-coded Mercury target. Agda `--safe` remains the only proof authority.

The existing `canonical-linear-haar-sparsemax-attention-composition-theorem` and `canonical-full-state-haar-sparsemax-invariant-composition-theorem` remain downstream source-derived composition certificates; they are not counted as additional new hypotheses in this pass.

The evidence boundary is therefore:

**empirical representation hypothesis** -> removed from the formal README claim surface

**source-derived theorem dependency** -> graph hypothesis

**Mercury A* + e-graph extraction** -> discovery/proof-plan evidence

**Agda `--safe`** -> proof acceptance

## Functional-programming physics methodology

Scott N. Walck's *Learn Physics with Functional Programming: A Hands-on Guide to Exploring Physics with Haskell* is used only as a methodology reference for typed functional modeling: make mathematical state, transformations, and invariants explicit in the program structure. The book was published by No Starch Press in 2023 (ISBN-13 9781718501669). Official publisher reference: https://nostarch.com/node/632. It is not treated as evidence for any theorem about this learner's computational power or for the Haar/A* certificates above.

The useful transfer is methodological rather than bibliographic: encode the mathematical object first, give the transformation an explicit type, and make the invariant a separately checkable equality. That matches the repository's division of labor between Agda proof terms, Mercury semantic/e-graph discovery, and typed functional CI orchestration.

## CI lanes

Roc dispatches four connected lanes:

`agda-safe`, `mercury`, `discovery`, and `surface`.

The Agda lane checks the canonical learner and theorem monolith with `agda --safe`.

The Mercury lane runs the theorem-policy gate.

The discovery lane runs theorem-only semantic extraction, A* cost-guided dependency-path search, e-graph insertion, saturation, analysis, and cost-guided extraction. The sync report is required to state `forced_symbolic_target=false`, `single_agda_source=true`, `astar_score_ordered=true`, and a positive emergent composition count.

The semantic-contract lane checks required theorem declarations directly in `TheoremsMonolith.agda` and rejects forbidden unrelated learner mechanisms. The surface lane derives its file inventory from `git ls-files`, rejects retired script/source languages, rejects a second generated theorem monolith, and requires `.ci/actions_ci.roc`.

## Deliberate mathematical boundary

The strict surface does not import a general topology hierarchy, Sion's minimax theorem, generic strong-convexity/coercivity machinery for modular `Int8` state updates, or reservoir literature.

Where a result is conditional, the condition is explicit. Where a global claim is impossible under finite `Int8` observation, the theorem says so rather than hiding the contradiction.


## Agda proof lane update

The proof lane uses the repository flake for the pinned Nix package environment, while the official Agda setup action installs Agda 2.8.0.2 and standard-library 2.4. The GitHub runner installs Nix with the NixOS-maintained nix-installer action, pinned by commit, and the workflow pins Nix 2.35.1.

The bounded exact-UAP surface includes exact retraction, decoder-transport, and postcomposition. The minimal bounded theorem needs a left inverse for exact readout. The standalone universal certificate exposes continuous left-invertibility, explicit orbit-observation separation, and exact readout for every target; separation is derived from the left inverse, so it is a visible redundant contract rather than an extra mathematical assumption.


## Terminology boundary

The active proof model is ordinary reinforcement learning (RL). The legacy filesystem/module namespace `Exotic/ERL/FullCoupled/...` is retained only to avoid a broad path-and-module migration in the proof surface; the mathematics and documentation do not claim an evolutionary-RL mechanism.


## Reservoir-computing universality boundary

The present Agda result is different and exact. On the canonical Nat-indexed orbit, state equality implies index equality, while an `Int8` observation has only finitely many values. Therefore a global exact left inverse `inverse ∘ observe = id` is impossible on the whole orbit by pigeonhole. The theorem `canonicalNoGlobalInt8ContinuousLeftInverseOnDiscreteTopologies` strengthens the boundary by explicitly granting continuity under the discrete topologies: even then the finite observation cannot have a global exact left inverse.

Consequently:

`finite Int8 observation + infinite canonical orbit -> no global exact left inverse`

This is a cardinality contradiction, not a claim that chaotic reservoirs are required in every universal-approximation setting. The reservoir result explains the dense-discontinuity phenomenon in the continuous infinite-precision regime; the Agda theorem establishes the stricter finite-precision obstruction for this algebra.

## Equality-saturation e-graph boundary

The Mercury implementation now contains the standard equality-saturation stages that were previously missing from the repository-specific congruence structure: e-matching, rewrite application, repeated saturation to an endogenous fixed point, rebuilding/congruence maintenance, e-class analysis, and cost-guided extraction. The theorem-sync gate exercises the same pipeline against the source-derived in-memory semantic law set. It does not make Mercury a proof authority: Agda `--safe` remains authoritative.


## Topology, import, and reservoir-universality boundary

The topology statement did not require a heavyweight topology package. The canonical learner monolith defines a minimal `Topology` record directly, using only the existing `Data.Empty` (`⊥`), `Data.Unit` (`⊤`), and `Data.Product` (`Σ`, `×`) primitives. `Continuous` is an explicit property over those topologies. The discrete topology is now also instantiated explicitly; under it every function is continuous, which makes the finite-observation contradiction independent of any continuity failure.

The import history is intentionally minimal. The canonical theorem monolith needs `Data.List` because its learner-replacement theorem surface uses `List`; the learner monolith does not currently use `List` and no longer imports it merely for symmetry. `Data.List.Sort` is not part of the current canonical proof lineage, and the older ordered-algebra work used custom `_≤_`/`_<` relation fields rather than a `Data.List.Sort` dependency. Those older ordered structures are not silently required by the exact-UAP proof.

For this repository's exact finite algebra the stronger obstruction is cardinality. The canonical orbit is injectively indexed by `Nat`, while `Int8` has only 256 values. Hence a global exact observation left inverse is impossible. Granting both observation and inverse continuity under the explicit discrete topology does not change that result. Chaotic internal dynamics also cannot evade the theorem while the exact observation remains `Int8`: the final observation map still has finite codomain.

## Mercury proof-source synchronization

Mercury semantic extraction now checks that `Exotic/ERL/FullCoupled/TheoremsMonolith.agda` explicitly declares `{-# OPTIONS --safe #-}` before building the in-memory semantic law set. The theorem e-graph then consumes that source-derived semantic law set and exercises e-matching, rewrite application, saturation, rebuild, e-class analysis, and cost-guided extraction. Agda remains the proof authority; Mercury is the semantic synchronization/equality-saturation verification layer.

## Model class, topology, Nat cardinality, and reservoir distinction

The active model is a learned recurrent finite-state/Mealy-style RL system: the learner monolith defines a `RecurrentNetwork` and a canonical GRU over finite `Int8`-valued components. The proof is not a reservoir-computing theorem, and the `ERL` filesystem namespace is legacy naming rather than an evolutionary-RL claim.

The topology construction is already minimal and constructive. `Topology` is defined directly using the existing `Data.Empty` (`⊥`), `Data.Unit` (`⊤`), and `Data.Product` (`Σ`, `×`) primitives; `Continuous` is then an explicit property over the two supplied topologies. No general topology package was imported. The discrete topology is instantiated explicitly, and every function is continuous for it. This is the clean counterpoint to treating continuity as synonymous with numerical precision.

The order/inequality imports are also deliberately small: `Data.Nat` supplies `_<_`, `_≤_`, and the finite arithmetic relations, while `Data.Nat.Properties` supplies the specific arithmetic lemmas already used. Historical canonical sources use that same family of imports. There is no current `Algebra.Order`, ordered-semiring, or `Data.List.Sort` dependency in the proof lineage. The recent `Data.List` correction was a separate asymmetry: `Data.List` is no longer imported by the theorem monolith after pruning the learner-replacement semantic block.

`Nat` is countably infinite, so an observation into `Nat` can avoid the finite-codomain pigeonhole obstruction that blocks global exact recovery through `Int8`. But infinite codomain is not sufficient for exact universal approximation. Exact universality still follows from composition with a left inverse: the standalone `ExactUniversalApproximationThroughContinuousLeftInverse` certificate provides continuous left-invertibility, derived observation separation, and exact readout for every target. The canonical infinite `Nat` orbit then supplies the contrasting countably infinite state index used in the finite-`Int8` contradiction.

### Reservoir-computing comparison

The reservoir literature is useful as a boundary comparison, not as the model class of this repository. Sugiura et al. 2025 prove, under their continuous-time reservoir-computing assumptions, equivalence among universality, the neighborhood separation property (NSP), and a uniformly continuous left inverse. They also prove dense discontinuity points for universal reservoir functionals. The 2024 predecessor explicitly constructs a universal reservoir with a single output, so 'universality implies infinite width' is not a theorem of that literature. [2025 necessary-and-sufficient reservoir theorem](https://www.mdpi.com/2227-7390/13/21/3440) [2024 finite-output universal reservoir theorem](https://www.nature.com/articles/s41598-024-56742-7)

The requested stronger statement — that infinite width and NSP are universal duals, both necessarily requiring infinite data, and that NSP intrinsically requires infinite numerical precision — is not established by those papers and is false as an unrestricted mathematical claim. In the 2025 theorem, the NSP is a metric/topological condition on an input-function space; it is not a statement about sample-count cardinality. Moreover, the abstract topological notion is not inherently an infinite-precision object: finite discrete spaces have perfectly meaningful open neighborhoods and every map between them is continuous. What does require unbounded resolution is a separate implementation claim for arbitrary fine separation in a non-discrete, real-valued metric representation.

For this repository the formal result is stronger and simpler: an injective `Nat`-indexed canonical orbit cannot admit a global exact left inverse through finite `Int8`. Granting continuity for both observation and inverse under the explicit discrete topology does not change that contradiction. Thus the exact obstruction is finite codomain cardinality, not lack of chaotic dynamics.

## Mercury synchronization boundary

Mercury now treats the `{-# OPTIONS --safe #-}` theorem monolith as the proof-source contract. The extractor verifies the safe declaration, recognizes the record-valued exact-UAP certificate, and derives the in-memory semantic law set directly from the theorem monolith only. The theorem e-graph derives dependencies from declaration signatures/bodies, enumerates maximal simple dependency paths, inserts every source law and graph plan, then runs e-matching, rewriting, fixed-point saturation, rebuild, e-class analysis, and cost-guided extraction. Agda `--safe` remains authoritative; Mercury is synchronized semantic/equality-saturation verification.

## Theorem-only equality saturation and canonical composition

Mercury's semantic extractor now reads only `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`. `CanonicalLearnerMonolith.agda` remains the sole owner of learner state and transitions; the theorem monolith imports those definitions, but Mercury does not e-graph the learner declarations themselves. Attention, Walsh-Hadamard attention mixing, and Walsh-Rademacher phase mixing are intentionally absent from the canonical learner.

The theorem monolith exposes `CanonicalGRUF4NormWatkinsPrefixCompositionTheorem`. It composes the recurrent prefix homomorphism, exact Watkins-target signal law, and the GRU × F4 optimizer × NormPair prefix bridge. The composition is source-derived and attention-free; Mercury discovers it from theorem declarations rather than from a hard-coded theorem-name registry.

The prefix complexity statement is exact: `recurrentPrefixStepWork n ≡ n` and the work splits additively over `m + n`. It is a finite equality certificate, not an invented asymptotic or statistical complexity claim.

`Nat` is the standard natural-number carrier with its usual addition/multiplication and order structure. Agda's standard library exposes `<` and `≤` and a large arithmetic/algebraic property surface in `Data.Nat.Properties`. [Data.Nat.Base](https://agda.github.io/agda-stdlib/v2.4/Data.Nat.Base.html) [Data.Nat.Properties](https://agda.github.io/agda-stdlib/v2.4/Data.Nat.Properties.html) The repository imports only the properties actually used by the proof. Importing a whole library module does not automatically create e-graph semantics: only declarations present in the theorem monolith and their extracted dependencies become e-graph nodes.

The finite-capacity contradiction is not that Nat is the wrong algebra. Nat can represent arbitrarily large integers and therefore unbounded bit-length. The contradiction is that an injective Nat-indexed orbit cannot be passed through a feature map whose information has an injective code into finite `Fin bound`; the resulting `Nat → Fin bound` map cannot be injective. `Int8` is the concrete finite special case.

No Sion theorem, regret bound, or statistical sample-complexity theorem is part of this exact theorem surface. The existing Bellman-Shapley inclusion theorem remains an explicit operator/inclusion contract with its own comparison and monotonicity hypotheses. Sion's theorem is not silently imported because the required topological convexity/semicontinuity assumptions are not part of the canonical learner proof.

No CHAD/automatic-differentiation theorem family is imported into this canonical learner/theorem graph. The current repository proof surface contains no CHAD source, and complexity results are stated only where an exact theorem already exists in the canonical theorem monolith.


The Nix CI invokes Mercury discovery only against `TheoremsMonolith.agda`. `CanonicalLearnerMonolith.agda` is kernel-checked because it is the canonical imported learner definition, but learner declarations are not inserted into the Mercury in-memory semantic law extraction or e-graph. No Sion-style environment-dependent regret or statistical sample-complexity theorem is part of this exact surface; no regret theorem is retained.

### Injectivity and finite-capacity boundary

The theorem monolith contains several distinct injectivity surfaces: Nat successor/cancellation used by the orbit proof, canonical orbit injectivity, discrete-left-inverse injectivity, continuous-left-inverse injectivity, exact-UAP-to-left-inverse equivalence, generic left-inverse observation injectivity, and orbit-observation separation. The finite-feature theorem then composes that injectivity with an injective code into `Fin bound` to obtain the pigeonhole contradiction. These are exact theorem transports, not mutually exclusive “algebra choices.”

The obstruction is specifically finite capacity. `Nat` can inject into an infinite ring such as the integers; it cannot inject into a finite carrier. If a ring algebra has (B) elements, its ring operations are irrelevant to the pigeonhole step once its carrier is finite.

`Data.Fin` is imported because finite carriers and finite sample indices are explicit theorem semantics. `Data.Vec` is not imported merely for Mercury search convenience: Mercury consumes declarations extracted from `TheoremsMonolith.agda`, not the declarations made available by arbitrary imports. A theorem that actually uses vectors can import the smallest `Vec` module/property set required by that theorem.


## AQLoop versus Mercury e-graph

`CanonicalAQLoopTheorem` is an Agda semantic certificate containing exact equalities for the canonical learner composition. The Mercury e-graph is a separate discovery and equality-saturation representation over extracted theorem declarations. E-graphs compactly represent equivalence classes and equality saturation repeatedly applies rewrites before extraction; they do not define the learner semantics in this repository. citeturn601944search0turn601944academia54

## Computational-capacity boundary

The Nat-indexed orbit, exact iterate composition, left-inverse injectivity, and finite-feature pigeonhole contradiction do not constitute a Turing-completeness theorem. No universal-machine interpreter, two-counter simulation, or compression=prediction theorem is formalized. The present result is an exact algebraic capacity boundary between unbounded Nat bit-length and finite feature cardinality.

## Current monolith/e-graph contract

The canonical learner remains exactly one executable source, `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`, and the canonical theorem surface remains exactly one public facade, `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`. `TheoremsMonolith/Part1a` through `Part5` are CI compilation partitions only; they are not separate learner semantics.

The theorem/e-graph boundary reads only the canonical `TheoremsMonolith.agda` source. Mercury graph search has no named theorem target, hard-coded dependency list, lookup table, fixed depth, or candidate-count cap: it seeds non-reflexive laws, follows declaration-derived dependencies, and hands every maximal simple dependency path to the hash-consed e-graph for saturation and extraction. Agda `--safe` remains the semantic authority; a Mercury candidate is not reported as an Agda theorem until the kernel checks the source theorem.

The Tsallis-2 measure is no longer conceptually restricted to the canonical two-action specialization. `ActionWeights d = Fin d -> Nat` provides the general exact finite-action definition; the existing two-action policy remains a specialization of the learner semantics rather than the definition of the measure. The hard support sparsity boundary is `(d-k)/d`; Tsallis-2 is the weighted effective-support measure `(dQ-S²)/(dQ)`, with the zero-vector convention equal to 1.

CI predecessor handoff is interface-only: theorem jobs consume downloaded `.agdai` artifacts and hide predecessor `.agda` sources before checking the current partition. This is specifically to prevent repeated canonical learner recompilation on the GitHub runner while preserving kernel-checked Agda interfaces and the separate Mercury stack.


## Non-iid stationary Markov/Walrasian composition

The theorem monolith now contains `ContinuousStationaryMarkovWalrasianData` and `continuousStationaryWalrasian-lift`. The transition is arbitrary; the only stationarity condition is invariance of the aggregate functional. Continuity is carried through the existing `Continuous` seam rather than assuming an iid-uniform shock law. The theorem proves the exact static-Walrasian-to-stationary-Walrasian lift; existence of a stationary law and existence of a Walrasian equilibrium remain separate hypotheses for future structural composition.

## Current endogenous graph composition gate

The canonical CI order is Agda `--safe` first, followed by theorem-only Mercury. Mercury consumes only semantic declarations extracted from `TheoremsMonolith.agda`; it does not import or e-graph the learner monolith. The graph stage seeds every non-reflexive law and follows declaration-derived dependencies without a named theorem target. The hash-consed e-graph then inserts every law and every maximal simple dependency plan, saturates to an endogenous fixed point, and extracts all source-derived laws. CI requires the non-forced report flag and a positive emergent-composition count.

The new theorem composition crosses four interfaces already present in the canonical theorem surface: recurrent associative prefix scanning, direct-product finite-automaton composition, continuous left-inverse exact readout, and arbitrary-transition stationary Markov/Walrasian lifting. The Markov result does not assume iid uniform shocks; it requires an invariant aggregate functional. The representation/stability boundary is explicit: continuous injective exact representation does not imply convergence of an arbitrary update rule, so it is not promoted into a Baird-stability theorem without an algorithmic contraction/convergence hypothesis.

A Bondareva–Shapley result is not reported as emergent merely because a game-theory theorem exists elsewhere. The current Mercury input is the canonical Agda theorem monolith, so a Bondareva–Shapley candidate becomes an endogenous discovery only after its relevant balancedness/core semantics are represented there and a source-derived graph proof plan actually connects them.

## Full commuting-square completion boundary (2026-09-21)

The theorem-only surface now contains a kernel-checkable generic commuting-square completion: `observe (step s) ≡ featureStep (observe s)`. Agda proves the induced iterate/naturality law by induction. A left inverse upgrades the square to exact reconstruction of the state transition on the observation image; adding a right inverse closes the square globally and gives exact conjugacy. This is the closest standard literature class to the requested equivalence square: equivariance/naturality in geometric deep learning and semiconjugacy/conjugacy in dynamical systems. The square law itself is not claimed as a new literature concept.

The repository-specific composition is the `--safe` combination of that generic square with the canonical finite-`Int8` observation boundary, Nat-indexed aperiodic orbit, recurrent prefix laws, and the existing optimizer/L2 + NormPair + biased Watkins/negative-q-Munchausen target composition. The finite-`Int8` result is definitive: global exact left inversion implies injectivity, while the canonical Nat-indexed orbit is infinite and the observation codomain is finite, so the global decoder cannot exist. No topology is needed for this contradiction; continuity can be supplied as an extra property and does not alter the cardinality obstruction.

The current model is a deterministic recurrent state-transition system. Its `RecurrentNetwork` interface has arbitrary state/input carriers, unlike a finite Mealy machine, and it has no required finite-state/output-function restriction. A finite-state instance plus an output map recovers the usual automata setting. The canonical learner has an unbounded Nat clock, so “general deterministic recurrent state machine” is more precise than “Mealy machine”; it remains an RNN/recurrent-network formulation in the repository's own formal interface.

The formal surface does not prove Turing completeness or super-Turing computation. The Nat clock supplies unbounded state cardinality, yet no universal-machine simulation, tape/counter encoding with the required control operations, or oracle/advice semantics is formalized. Siegelmann–Sontag establish Turing simulation for particular rational-weight recurrent networks and super-Turing behavior in idealized real/analog settings; Cabessa/Siegelmann and related work obtain super-Turing results under interactive/evolving assumptions. Those hypotheses are not established by this finite-precision canonical learner.

The current proof source remains exactly `TheoremsMonolith.agda`; Mercury remains theorem-only equality-saturation/discovery, with Agda `--safe` as proof authority. The duplicated recovered component-prefix block was pruned. The Mercury sync parser was corrected so the gate can reach semantic/e-graph checks rather than failing at Mercury syntax.
## Computational-power and functional-programming literature review (2026-09-21)

Scott N. Walck's *Learn Physics with Functional Programming* is relevant as a methodology reference: the book uses Haskell's type system, higher-order functions, and referential transparency to encode physical mathematics and state-update calculations. It was published by No Starch Press in January 2023. It is not a result about Turing completeness of recurrent learners, so it does not by itself establish a computational-power class for this repository. The useful transfer is the typed-functional-programming discipline: make the state transformation and its invariants explicit rather than treating them as informal implementation details.

For the one-transition algebra, the correct standard classification is stronger and more precise than merely saying “equivariant.” The additive monoid (N,+,0) is the free monoid on one generator. A deterministic transition `step : State -> State` therefore induces an N-action by iteration. If `observe (step s) ≡ featureStep (observe s)` holds for one generator, induction gives `observe (step^n s) ≡ featureStep^n (observe s)` for every n. That is an equivariant map / homomorphism of the generated free-monoid actions. The repository now has the explicit `FreeMonoidActionHomomorphism` theorem for this statement.

Conjugacy is a further condition, not a consequence of the one-step square alone. A left inverse makes the observation injective and yields an exact reconstruction/embedding. A two-sided inverse gives an isomorphism of the state and feature dynamical systems, i.e. conjugacy. The repository's `FullCommutingSquareConjugacyTheorem` formalizes exactly that distinction. The canonical learner currently has the generic theorem schema and the concrete clock-action homomorphism; it does not have a global two-sided state/feature inverse through `Int8`, because the finite-observation contradiction rules that out.

The computational-power literature establishes why the distinction matters. Siegelmann and Sontag (1995) prove Turing simulation for particular finite-size recurrent neural nets with sigmoidal processors and rational coefficients; their result is not a theorem about every RNN or every finite-precision recurrent system. Weiss, Goldberg, and Yahav (2018) analyze finite-precision RNNs under linear-time computation and distinguish the language-recognition power of several recurrent variants, including GRUs. Chung and Siegelmann (2021) recover Turing completeness for a bounded-precision RNN augmented with a dynamically growing memory module. Pérez, Marinković, and Barceló (2019) establish Turing completeness for Transformer and Neural GPU models under their formal representation assumptions. These results show that “RNN,” “finite precision,” or “dense representation” alone does not determine computational power.

For this repository, the definitive theorem currently proved is narrower and exact: an infinite Nat-indexed canonical orbit cannot have a globally exact injective representation through finite `Int8` together with an exact decoder. The proof is `encode : Nat -> State`, exact injectivity of `encode`, exact reconstruction `decode (observe (encode n)) ≡ encode n`, followed by the finite-`Int8` pigeonhole theorem. The optimizer, L2, NormPair, biased Watkins, and negative-q-Munchausen composition do not invalidate this contradiction: once the proposed computational representation still requires an injective Nat orbit to pass through finite `Int8`, cardinality alone defeats it.

That is not yet a theorem that the unrestricted canonical learner is strictly weaker than Turing machines. A strict computational-power comparison requires a formal machine class: an input encoding, admissible kernels/parameters, transition semantics, output/readout semantics, and a definition of what it means to simulate or decide a language. The current Agda surface does not contain a universal-machine encoding or a proved simulation/separation theorem for that class. Therefore the exact claim is: **the finite-`Int8`, exact-left-invertible countable simulation class is provably empty; the unrestricted learner class has not been proved Turing-incomplete or Turing-complete.** This is a completed mathematical distinction, not an unresolved appeal to super-Turing models.

The deterministic pigeonhole result is Agda-kernel proof, not a Mercury proof. Mercury's A*-style e-graph search can discover and compose the theorem because the declaration and dependency graph exposes it, but Mercury does not replace the `--safe` kernel. In particular, “surjectivity” is not inferred from pigeonhole alone: the established result is non-injectivity of a map from an infinite Nat-indexed set into a finite carrier. Surjectivity must be separately stated and proved for a particular map.

The current new theorem class is therefore:

`one-step commuting square`
→ `free-monoid action homomorphism`
→ `recurrent prefix homomorphism`
→ `exact Watkins target-prefix correctness`
→ `GRU × F4 × NormPair composition`
→ `left-inverse ⇒ injectivity`
→ `finite-Int8 pigeonhole obstruction`.

The generalized stationary Markov/Walrasian class is orthogonal but composable: arbitrary transition + invariant aggregate + static Walrasian equilibrium gives the explicit stationary generalized equilibrium object, while conjugate representation transport preserves it only under the stated transport witness. No unconditional Walrasian existence theorem is silently claimed.
