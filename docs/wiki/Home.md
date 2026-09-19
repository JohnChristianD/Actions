# Actions: Canonical Learner, Semantic Discovery, and Proof Environment

Last audited: 2026-09-19 against \`main\` at \`d48e5cf6e3671f268440135f1acc32eeafb3d510\`.

Git currently reports no combined status entries for this head, so the wiki does not label the current remote workflow run green.

## Single active theorem source

The canonical theorem entrypoint is:

\`Exotic/ERL/FullCoupled/TheoremsMonolith.agda\`

It imports \`CanonicalLearnerMonolith.agda\` and packages the active canonical learner laws: policy and sparsemax laws, Walsh/phase laws, GRU preservation and composition laws, full-step projections, endogenous attention/Watkins/GRU/F4 coupling, clock growth, aperiodicity, the finite TSTS connected theorem, the intrinsic attention-mediator theorem, the recurrent prefix theorem, and the finite reservoir-faithfulness boundary.

\`GeneralFullCoupledTheoremsMonolith.agda\` is a separate generalized/benchmark theorem surface. It is not the canonical theorem entrypoint.

## Current learner implementation

The active canonical implementation is:

- \`Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda\`
- \`Exotic/ERL/FullCoupled/CanonicalGamePorts.agda\`
- \`Exotic/ERL/FullCoupled/CanonicalFaithfulGameVariants.agda\`
- \`Exotic/ERL/FullCoupled/CanonicalClosedLoopBench.agda\`

There is no current \`CanonicalClosedLoopInterface.agda\` in the main tree. The older wiki wording that named it as an active component was stale.

The learner state and one-step transition live in \`CanonicalLearnerMonolith.agda\`. The benchmark module \`CanonicalClosedLoopBench.agda\` builds explicit finite closed-loop specifications and metrics over the learner and game ports.

## Canonical learner shape

The learner uses a finite \`Int8\` carrier represented by \`Fin 256\`, concrete records and finite data declarations, and propositional equality.

The canonical state is:

\`\`\`
FullLearnerState
  clock
  watkins
  attention
  gru
  optimizer
  norm
  lcbCounts
  qLogControl
  qLogValue
\`\`\`

\`canonicalFullStep\` increments the clock, updates Watkins state, attention, GRU, optimizer, LCB counts, Q-log control, and Q-log value, while preserving the \`NormPair\`.

The canonical policy is fixed-temperature sparsemax over the LCB-adjusted critic. Learned sparsemax attention is a separate channel. Attention enters the endogenous loop through Walsh-Hadamard mixing and the finite four-phase Walsh/Rademacher layer.

The endogenous Watkins target combines canonical reward, Q-log bias, discounted critic maximum, and \`canonicalEndogenousFeedback\`. The same signal feeds the Watkins update, GRU update, and F4/L2 optimizer update.

## Finite benchmark seam

\`CanonicalGamePorts.agda\` defines exact finite port states and transition functions, including Maze, FourRooms, Level-Based Foraging, Pong, Memory Chain, Discounting Chain, CartPole, Bernoulli Bandit, RockSample, Knapsack, and other finite port carriers.

\`CanonicalFaithfulGameVariants.agda\` contains exact finite predicates for Toy Maze and FourRooms layouts.

\`CanonicalClosedLoopBench.agda\` defines:

- \`ClosedLoopSpec\`
- \`ClosedLoopRun\`
- \`ClosedLoopMetrics\`

and composes those explicit ports with \`FullLearnerState\`.

"Faithful" means exact formal interface closure and finite predicates. It does not prove external simulator behavioral equivalence.

## Mercury, Guix, and Agda

The current execution architecture is:

\`\`\`
pinned Guix environment
        |
        v
Guile CI driver
        |
        +--> Mercury semantic extraction/discovery checks
        |
        +--> Mercury generic e-graph regressions
        |
        +--> generated Agda artifact audit
        |
        v
Agda --safe
        |
        v
proof acceptance
\`\`\`

Agda is the authority for learner semantics and theorem acceptance. Mercury is outside the Agda kernel trust boundary.

The important semantic constraint is that Mercury does not own a hard-coded learner symbol registry or a hard-coded theorem grammar. The current discovery executable reads the semantic manifest generated directly from the canonical learner and theorem source.

## Current semantic discovery

The active Mercury discovery sources are:

- \`.ci/discovery/learner_semantic_extractor.m\`
- \`.ci/discovery/learner_semantic_manifest.m\`
- \`.ci/discovery/novel_learner_theorem_discovery.m\`

The extractor reads exactly:

- \`Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda\`
- \`Exotic/ERL/FullCoupled/TheoremsMonolith.agda\`

It recognizes theorem-like top-level signatures, records their source/name/signature/body, computes source-level identifier dependencies, and writes \`learner-semantic-laws.tsv\`.

The manifest parser turns those rows into typed Mercury \`semantic_law\` values.

The discovery executable then selects laws marked composite by the extracted dependency relation and generates aliases into:

\`Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda\`

The current generated module contains four derived aliases to existing canonical theorem declarations. The filename/report key still says "Novel", but the current executable semantics do not synthesize a new hand-authored learner transformation vocabulary. The generated surface is a semantic projection of existing declarations, not an independent symbolic ontology.

## Generic symbolic e-graph

The current generic symbolic engine is:

- \`.ci/discovery/symbolic_egraph.m\`
- \`.ci/discovery/symbolic_egraph_test.m\`
- \`.ci/discovery/interpolated_theorem_egraph.m\`
- \`.ci/discovery/interpolated_theorem_egraph_test.m\`

\`symbolic_egraph.m\` provides generic enodes, expression trees, hash-consing, union-find representatives, congruence rebuild, equivalence checks, and size counts.

\`interpolated_theorem_egraph.m\` derives its expressions from the extracted semantic manifest. It encodes semantic-law identities and dependency composition plans. It does not define the learner's semantic symbols and does not enumerate an external transformation grammar.

Therefore the symbolic layer is subordinate to the learner source:

\`\`\`
canonical Agda declarations
        |
        v
automatic semantic extraction
        |
        v
typed semantic manifest
        |
        v
optional generic symbolic normalization
        |
        v
generated Agda declarations
        |
        v
Agda --safe
\`\`\`

## Guix verification lanes

\`.guix/ci.scm\` defines four lanes:

- \`agda-safe\`
- \`mercury\`
- \`discovery\`
- \`surface\`

The Agda lane regenerates the semantic-discovery artifact, audits its proof shape, type-checks the listed Agda surface with \`agda --safe\`, and type-checks the generated theorem module.

The Mercury lane runs the forbidden-theorem scanner and the manifest-driven discovery machinery.

The discovery lane runs the semantic discovery plus generated-artifact audit.

The surface lane rejects repository source files in the retired Haskell, Python, JavaScript/TypeScript, JVM-language, Elm, and PureScript suffix families.

The Guix manifest pins Agda 2.7.0.1, Agda standard library 2.3, Mercury 22.01.4, Guile 3.0, and Git.

## Repository consistency note

The current \`.guix/ci.scm\` still lists \`Exotic/ERL/FullCoupled/CanonicalClosedLoopInterface.agda\` in its \`agda-safe-files\` list even though that path is absent from the current \`main\` tree. This is a live CI configuration mismatch, so the wiki records it rather than silently treating the configured safe lane as fully current.

## Legacy and generalized surfaces

\`GeneralFullCoupledLearnerMonolith.agda\`, \`GeneralFullCoupledTheoremsMonolith.agda\`, and \`GeneralClosedLoopBenchV2.agda\` remain useful generalized benchmark/formalization surfaces.

They should not be conflated with the canonical learner monolith or the canonical theorem monolith.

## CleanRL / LeanRL relationship

The repository uses a single explicit canonical learner source and a single explicit canonical theorem source. It does not reproduce CleanRL or LeanRL as a software architecture.

The formal boundary is intentionally concrete: learner semantics in Agda, deterministic verifier/discovery tooling in Mercury, and reproducible orchestration in Guix/Guile.
