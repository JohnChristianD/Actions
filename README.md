# Actions - Exact Recurrent Learner and Theorem-Graph Monograph

This repository formalizes a bounded recurrent learner, exact sequence-model semantics, finite-observation information boundaries, optimizer composition, probability semantics, POMDP transport, and theorem discovery.

The canonical proof surface is Agda. Mercury extracts the declarations that Agda exposes, searches dependency paths, and builds e-graph candidates. Dhall declares the verification contract. Nix composes the reproducible build environment. GitHub Actions executes the configured checks.

A discovered graph path is not a proof. A candidate becomes authoritative only when the corresponding proposition is present on the Agda proof surface and accepted by the Agda checker.

## Language roles

### Agda

Agda is the semantic and proof authority.

The canonical learner definitions are in:

```
Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
```

The canonical theorem surface is:

```
Exotic/ERL/FullCoupled/TheoremsMonolith.agda
```

This role is chosen because dependent types let the project encode propositions and their proofs in one type-checked language. The theorem monolith is also explicitly declared with Agda's safe mode. Safe mode excludes several mechanisms that could bypass ordinary consistency checks, including postulates and unfinished proof holes. The result is a narrow proof authority rather than a general-purpose automation language.

Agda is not used for graph search or CI orchestration. Keeping those concerns outside the proof kernel reduces the authority surface.

### Mercury

Mercury is the semantic extraction and graph-search engine.

The discovery programs under `.ci/discovery/` parse the theorem monolith, identify declarations and dependencies, classify composite laws, run dependency searches, construct e-graph candidates, and perform cost-guided extraction.

Mercury is well matched to this role because its type, mode, and determinism declarations are compiler checked. The language also has a declarative semantics, so the search machinery can be written as typed predicates with explicit data-flow and solution-count contracts.

Mercury is not the proof authority. It can discover a useful dependency path without establishing the mathematical proposition represented by that path.

### Dhall

Dhall is the CI policy language.

`.ci/actions_ci.dhall` declares the verification lanes, commands, theorem graph gates, and other checks that the repository expects CI to execute.

Dhall is useful here because configuration evaluation is intentionally much narrower than arbitrary general-purpose program execution. It is total and strongly typed, which makes it suitable for expressing a machine-checked policy without giving the policy layer the same authority as the theorem prover.

Dhall therefore answers "what should CI require?" rather than "is this mathematical theorem true?"

### Nix

Nix is the reproducibility and environment-composition layer.

It defines the packages, toolchains, build inputs, and reproducible environment used by the project. That makes it the right boundary for controlling build variation rather than proof meaning.

Nix is not a theorem prover, semantic-law extractor, or CI policy authority.

### GitHub Actions

GitHub Actions is the execution substrate.

It schedules the configured workflows and runs the repository's checks. A successful workflow means the configured commands returned success. It does not independently establish the truth of an Agda proposition.

## Why these roles are separated

The safety claim is role-specific, not a claim that this is universally the safest programming-language stack.

For proof authority, Agda has the strongest fit in this stack because its type system directly represents proofs and safe mode removes several escape hatches.

For semantic search, Mercury has the strongest fit in this stack because types, modes, determinism, and declarative semantics constrain the search implementation itself.

For configuration policy, Dhall has the strongest fit in this stack because total evaluation and static typing constrain configuration computation.

For reproducible builds, Nix has the strongest fit in this stack because environment and dependency construction are its primary concern.

For workflow execution, GitHub Actions is appropriate because it is the repository's execution substrate rather than an additional semantic authority.

These are comparative role statements, not a literature-wide ranking. There is no sound basis for claiming that these languages are universally safer than every other language used for autonomous agents.

## What "CI declaration" means

A CI declaration is the declarative description of the checks that the continuous-integration system is required to run.

In this repository the layers are:

```
Dhall
  |
  | declares lanes, commands, and gates
  v
GitHub Actions
  |
  | schedules and executes workflows
  v
Nix
  |
  | supplies the reproducible environment
  v
Agda + Mercury + repository checks
  |
  +-- Agda: theorem and type authority
  |
  +-- Mercury: extraction, dependency search, e-graph and A* guidance
  |
  +-- other checks: repository-specific verification
```

Dhall can require that Agda passes. Dhall cannot prove an Agda theorem.

## Complete Agda theorem relationship

The graph below covers the theorem records currently declared in `TheoremsMonolith.agda`. It deliberately separates the foundational carrier/transport type from the theorem records.

```
Canonical learner and scan foundation
|
+-- CanonicalAQLoopTheorem
+-- CanonicalConnectedCompositionTheorem
+-- CanonicalLearnerReplacementClosureTheorem
+-- EqualityCompositionTheorem
+-- RecurrentAssociativeScanTheorem
+-- CanonicalGRUF4NormWatkinsPrefixCompositionTheorem
+-- CommutingSquareTheorem
+-- CommutingSquareLeftInverseTheorem
+-- FullCommutingSquareConjugacyTheorem
+-- RecurrentScanConjugacyTheorem
+-- CanonicalFullLearnerConnectedScanConjugacyTheorem
+-- S4PlusS5RecurrentScanTheorem
|
+-- Control, approximation, and computability
|   +-- MinimaxBellmanShapleyInclusionTheorem
|   +-- CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
|   +-- CanonicalQMunchausenL2SharedNegationPolarityTheorem
|   +-- DiscreteExactUAPTheorem
|   +-- DiscreteExactUniversalUAP
|   +-- DiscreteExactUniversalUAPLeftInverseEquivalence
|   +-- CanonicalExactCompositionTuringCompletenessContract
|   +-- ContinuousLeftInverseTheorem
|   +-- BoundedContinuousLeftInverseExactApproximationTheorem
|   +-- RingStateInjectivityTheorem
|   +-- DenseNeighborhoodSeparationTheorem
|   +-- CanonicalRecurrentBoundedExactUniversalApproximationTheorem
|   +-- CanonicalEndogenousMinimaxBellmanShapleyUAPTheorem
|
+-- Finite recurrence, equilibrium, and optimizer boundaries
|   +-- FiniteMixedProductRecurrenceTheorem
|   +-- AbsorbingFiniteEquilibriumTheorem
|   +-- HardSparseAbsorbingPrefixTheorem
|   +-- FiniteHardSparseKKTEquilibriumTheorem
|   +-- FiniteRankStabilityCertificate
|   +-- FiniteNonIIDWalrasianEquilibrium
|   +-- FiniteTUShapleyAllocationEquilibrium
|   +-- CanonicalPolymorphicSparsemaxCompositionTheorem
|   +-- DirectProductFiniteAutomatonComposition
|   +-- OffPolicyFunctionApproximationStabilityBoundary
|
+-- Equilibrium and conjugacy transport
|   +-- MarkovStationaryWalrasianCompositionTheorem
|   +-- GlobalConjugacyEquivalence
|   +-- GeneralizedWalrasianEquilibrium
|   +-- ConjugateWalrasianTransport
|   +-- Majority3ShapleyEquilibrium
|
+-- Token, recurrent-network, and finite-function transport
|   +-- CanonicalGlobalTokenConjugacyTheorem
|   +-- FiniteFunctionExactIsomorphismTransportTheorem
|   +-- FiniteRecurrentFunctionExactTranslationTheorem
|   +-- FinitePOMDPExactTransport
|   +-- ArchitecturePreservingCanonicalRNNLMIsomorphism
|   +-- CanonicalExactRNNLMTheorem
|   +-- CanonicalGlobalTokenLMCompositionTheorem
|
+-- Attention, Haar structure, and operator composition
|   +-- CanonicalIntegerHaarScaledOrthogonalityTheorem
|   +-- CanonicalAStarCostGuidanceTheorem
|   +-- CanonicalFullStateHaarSparsemaxInvariantCompositionTheorem
|   +-- CanonicalHaarSparsemaxFullStateClosureTheorem
|   +-- CanonicalLinearHaarSparsemaxAttentionCompositionTheorem
|   +-- CanonicalFiniteCycleExclusionIsomorphismTheorem
|   +-- CanonicalOperatorCompositionTheorem
|   +-- CanonicalBoundedFactorLiftTheorem
|   +-- FiniteFactorRecurrenceWithoutStateRecurrenceTheorem
|
+-- Endogenous observation and information boundaries
|   +-- CanonicalEndogenousObservationBoundaryTheorem
|   +-- CanonicalEndogenousTopologicalObservationBoundaryTheorem
|   +-- CanonicalPureNonOrangeBypassCompletionTheorem
|   +-- CanonicalFiniteObservationInformationBoundaryTheorem
|   +-- CanonicalExactTuringBoundaryMixtureTheorem
|   +-- CanonicalGlobalInt8LeftInverseImpossibilityTheorem
|
+-- Stationarity, persistent excitation, and computability
|   +-- FiniteObservationStationaryLimitTheorem
|   +-- CanonicalPersistentExcitationRequirementTheorem
|   +-- ExactContractComputabilityBoundaryTheorem
|   +-- CanonicalFiniteObservationStationarySubcompositionTheorem
|   +-- CanonicalClockObservationSubcompositionTheorem
|   +-- CanonicalBoundednessPEBoundarySubcompositionTheorem
|
+-- Probability and POMDP semantics
|   +-- FiniteProbabilityMassSemanticsTheorem
|   +-- FinitePOMDPProbabilitySemanticsTheorem
|   +-- FiniteBeliefUpdateExactTransportTheorem
|   +-- CanonicalEndogenousPOMDPObservationBoundaryTheorem
|
+-- RNN-LM capability closure
|   +-- CanonicalExactRNNLMCapabilitySubcompositionTheorem
|   +-- CanonicalExactRNNLMObservationSubcompositionTheorem
|   +-- CanonicalExactRNNLMObservationTopologyCapabilityTheorem
|   +-- CanonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem
|   +-- CanonicalTokenVocabularyUpperBoundTheorem
```

The theorem graph has two directions.

The semantic direction starts with executable definitions and exact local laws in Agda:

```
CanonicalLearnerMonolith
        |
        v
TheoremsMonolith
        |
        v
declared theorem records and laws
```

The discovery direction then reads those declarations without becoming a second proof authority:

```
TheoremsMonolith
        |
        v
learner_semantic_extractor
        |
        v
theorem_graph_search
        |
        +-- dependency paths
        +-- composite-law plans
        +-- endogenous-composition search
        |
        v
theorem_monolith_egraph_sync
        |
        +-- equality saturation
        +-- A* cost-guided extraction
        |
        v
candidate composition
        |
        v
Agda theorem declaration and checking
```

The current graph pre-registers all 77 theorem records above. The five dedicated subcomposition gates are:

```
CanonicalClockObservationSubcompositionTheorem
CanonicalFiniteObservationStationarySubcompositionTheorem
CanonicalBoundednessPEBoundarySubcompositionTheorem
CanonicalExactRNNLMCapabilitySubcompositionTheorem
CanonicalExactRNNLMObservationSubcompositionTheorem
```

This pre-graph is a gate and discovery index. It does not promote a graph path to a proof.

## Emergent endogenous closure

The current strongest cross-domain endogenous composition is:

```
CanonicalExactRNNLMTheorem
        |
        +-- CanonicalGlobalTokenLMCompositionTheorem
        +-- ArchitecturePreservingCanonicalRNNLMIsomorphism
        |
        v
CanonicalExactRNNLMObservationTopologyCapabilityTheorem
        |
        +-- CanonicalEndogenousObservationBoundaryTheorem
        +-- CanonicalEndogenousTopologicalObservationBoundaryTheorem
        +-- CanonicalFiniteObservationInformationBoundaryTheorem
        |
        v
CanonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem
        |
        +-- CanonicalEndogenousPOMDPObservationBoundaryTheorem
        |      |
        |      +-- FinitePOMDPProbabilitySemanticsTheorem
        |      +-- FiniteBeliefUpdateExactTransportTheorem
        |
        +-- CanonicalFiniteObservationInformationBoundaryTheorem
```

This is a composition of already declared exact surfaces. It is not a new primitive axiom and should be described as an emergent closure rather than as a newly discovered foundational law.

## Exact vocabulary capacity of this formulation

The canonical token carrier is:

```
CanonicalToken = Fin 256
CanonicalToken <-> Int8
```

The encode and decode functions are exact inverses. Therefore the formal vocabulary has exactly:

```
256 distinct token symbols
```

This is a theorem about this formulation's token carrier. It is not a claim about arbitrary language models.

The sequence type is `List CanonicalToken`. Consequently the model can represent arbitrarily long finite token sequences over the 256-symbol alphabet. The 256 bound concerns the vocabulary alphabet, not the number of possible sequences.

`CanonicalTokenVocabularyUpperBoundTheorem` currently proves the exact carrier equivalence. A separate numeric cardinality theorem would be a different statement; it should not be conflated with the carrier equality.

## Formal scope

The repository contains several deliberately separate readings:

- Recurrent learning: explicit learner state, policy readout, optimizer state, and observation maps.
- Informatics: recurrent prefixes and their composition.
- Dynamical systems: exact clock growth, cycle exclusion, conjugacy, finite-factor recurrence, and observation boundaries.
- Stochastic semantics: finite probability masses, finite POMDP kernels, and exact belief-update transport.
- Theoretical computer science: finite-carrier information limits and the explicitly stated exact-computability boundary.
- RNN-LM semantics: finite tokens, recurrent processing, logit traces, sparsemax operations, token-LM composition, and architecture-preserving transport.

These are formal structural correspondences. They are not claims of empirical language-model performance, biological validity, physical realism, or a general equilibrium theorem.

## Exactness policy

The repository does not treat an e-graph extraction as proof.

It also does not obtain a green result by weakening a theorem, replacing a missing proof with a trivial proposition, silently changing a carrier, or changing the semantic target merely to satisfy a graph gate.

The finite probability and POMDP layers are exact finite semantics. They are not a claim of full measure-theoretic probability.

The RNN-LM layers are exact formal capability and transport statements. They are not benchmark results.

## Repository surfaces

Canonical proof surface:

```
Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
Exotic/ERL/FullCoupled/TheoremsMonolith.agda
```

Discovery surface:

```
.ci/discovery/learner_semantic_extractor.m
.ci/discovery/theorem_graph_search.m
.ci/discovery/theorem_monolith_egraph_sync.m
```

Automation surface:

```
.ci/actions_ci.dhall
Nix configuration and build definitions
GitHub Actions workflows
```

The intended lifecycle is:

```
exact definition
    |
    v
Agda law and theorem
    |
    v
semantic extraction
    |
    v
dependency graph search
    |
    v
e-graph and A* candidate extraction
    |
    v
Agda promotion and checking
    |
    v
CI execution
```

The proof, discovery, policy, environment, and execution layers remain separate by design.
