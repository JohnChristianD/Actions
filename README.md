# Actions - Exact Recurrent Learner and Theorem-Graph Monograph

This repository formalizes a bounded recurrent learner, exact sequence-model semantics, finite-observation information boundaries, optimizer composition, probability semantics, POMDP transport, and theorem discovery.

The canonical proof surface is Agda. Mercury extracts the declarations that Agda exposes, searches dependency paths, and builds e-graph candidates. Dhall declares the verification contract. Nix composes the reproducible build environment. GitHub Actions executes the configured checks.

A discovered graph path is not a proof. A candidate becomes authoritative only when the corresponding proposition is present on the Agda proof surface and accepted by the Agda checker.

## Language roles and why these choices fit

### Agda: proof and semantic authority

Agda is used for the canonical learner definitions and theorem surface:

```
Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
Exotic/ERL/FullCoupled/TheoremsMonolith.agda
```

This is the strongest role match in this stack for proof authority because dependent types represent propositions as types and proofs as ordinary type-correct terms. The repository runs the theorem surface with `--safe`. Safe Agda disables mechanisms such as postulates, unfinished metas, skipped termination checks, and several other consistency escape hatches. Agda also mechanically checks termination for accepted recursive definitions.

Agda is kept out of graph search and CI orchestration. The language that establishes proof correctness is therefore not also the language that invents the candidate dependency path.

This is a role-specific claim, not a universal claim that Agda is the safest language for every autonomous-agent task. It is the best fit here because the critical asset is a machine-checked proof object.

### Mercury: semantic extraction and graph search

Mercury implements the discovery layer under `.ci/discovery/`.

Its type, mode, determinism, purity, and declarative-semantics machinery make it a strong fit for a search engine whose own behavior should have explicit contracts. The Mercury compiler checks type, mode, and determinism declarations, and Mercury defines a declarative semantics for legal programs.

Modes constrain data flow, determinism constrains solution counts, and purity constrains ordinary computations to explicit effects. This is a stronger static contract for the graph engine than an ordinary dynamically typed scripting layer would provide.

Mercury remains subordinate to Agda. It discovers, classifies, ranks, and extracts candidates; it does not certify the mathematical proposition.

### Dhall: CI policy

Dhall is used for `.ci/actions_ci.dhall`.

A CI declaration is a typed, declarative specification of the verification lanes, commands, and gates that CI is required to execute. Dhall is a strong fit for this boundary because it is a total functional configuration language rather than a Turing-complete scripting environment. Its type system and finite evaluation model constrain configuration failures before the configuration is consumed.

Dhall can require Agda, Mercury, graph checks, and other tests to pass. It cannot itself prove an Agda theorem.

### Nix: reproducible environment

Nix defines the toolchain and build environment.

The Nix language is pure, functional, declarative, and lazy. Nix derivations describe build inputs and outputs, while the Nix store gives dependency results stable identities based on their dependency graph. This makes Nix a strong fit for reproducible environment construction without making it part of theorem semantics.

Nix is not a proof authority or semantic checker. Its safety value here comes from keeping environment construction separate and reproducible.

### GitHub Actions: execution substrate

GitHub Actions is the outer execution layer. It schedules workflows and runs the commands declared by the repository policy.

It is intentionally not treated as a semantic authority. A successful workflow means the configured commands completed successfully under the configured environment; it does not independently prove an Agda proposition.

## Why the stack is split

```
Agda
  |
  | proves and type-checks
  v
Mercury
  |
  | extracts, searches, saturates, ranks
  v
Dhall
  |
  | declares required checks
  v
Nix
  |
  | supplies the reproducible environment
  v
GitHub Actions
  |
  | executes the declared checks
  v
verification result
```

The arrows describe orchestration, not mathematical implication. In particular, a Mercury e-graph result cannot become a theorem merely because a path was found.

## Complete Agda record relationship graph

The canonical theorem monolith currently contains 95 top-level record declarations.

The following graph is derived from the actual record declarations and their direct record-to-record references. Every record is listed exactly once. This includes foundational data records, theorem contracts, transport structures, problem specifications, and composition records. Non-record definitions are not disguised as theorem records.

```
01. CanonicalAQLoopTheorem
02. StateIsomorphism
03. CanonicalConnectedCompositionTheorem
    +-- depends on: CanonicalAQLoopTheorem
04. CanonicalLearnerReplacementClosureTheorem
05. EqualityCompositionTheorem
06. RecurrentAssociativeScanTheorem
07. RecurrentPrefixMonoidHomomorphism
08. CanonicalGRUF4NormWatkinsPrefixCompositionTheorem
    +-- depends on: RecurrentPrefixMonoidHomomorphism
09. CommutingSquareTheorem
10. CommutingSquareLeftInverseTheorem
    +-- depends on: CommutingSquareTheorem
11. FullCommutingSquareConjugacyTheorem
    +-- depends on: CommutingSquareTheorem
12. FreeMonoidActionHomomorphism
13. ObservationTaskFactorization
14. RecurrentScanConjugacyTheorem
15. CanonicalFullLearnerConnectedScanConjugacyTheorem
16. S4PlusS5RecurrentScanTheorem
    +-- depends on: RecurrentAssociativeScanTheorem
17. PointwiseSandwich
18. MinimaxBellmanShapleyOperator
19. MinimaxBellmanShapleyInclusionTheorem
    +-- depends on: PointwiseSandwich, MinimaxBellmanShapleyOperator
20. CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
21. CanonicalQMunchausenL2SharedNegationPolarityTheorem
22. DiscreteExactUAPTheorem
23. DiscreteLeftInverseWitness
24. DiscreteExactUniversalUAP
25. DiscreteExactUniversalUAPLeftInverseEquivalence
    +-- depends on: DiscreteLeftInverseWitness, DiscreteExactUniversalUAP
26. ExactNatObservationSimulation
27. ExactTuringCounterObservation
28. ExactTwoCounterConfiguration
29. ExactTwoCounterMachine
    +-- depends on: ExactTwoCounterConfiguration
30. CanonicalExactCompositionTuringCompletenessContract
    +-- depends on: ExactTwoCounterConfiguration, ExactTwoCounterMachine
31. ContinuousLeftInverseTheorem
32. BoundedContinuousLeftInverseExactApproximationTheorem
    +-- depends on: ContinuousLeftInverseTheorem
33. RingStateInjectivityTheorem
34. DenseNeighborhoodSeparationTheorem
35. CanonicalRecurrentBoundedExactUniversalApproximationTheorem
    +-- depends on: RecurrentAssociativeScanTheorem, ContinuousLeftInverseTheorem, DenseNeighborhoodSeparationTheorem
36. CanonicalEndogenousMinimaxBellmanShapleyUAPTheorem
    +-- depends on: PointwiseSandwich, MinimaxBellmanShapleyOperator, MinimaxBellmanShapleyInclusionTheorem, CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem, DiscreteExactUAPTheorem, ContinuousLeftInverseTheorem, BoundedContinuousLeftInverseExactApproximationTheorem, RingStateInjectivityTheorem, DenseNeighborhoodSeparationTheorem, CanonicalRecurrentBoundedExactUniversalApproximationTheorem
37. FiniteMixedProductRecurrenceTheorem
38. AbsorbingFiniteEquilibriumTheorem
39. HardSparseAbsorbingPrefixTheorem
40. FiniteHardSparseKKTEquilibriumTheorem
41. UniqueKKTAbsorbingClass
42. FiniteRankStabilityCertificate
43. FiniteNonIIDWalrasianEquilibrium
44. FiniteTUShapleyAllocationEquilibrium
45. CanonicalPolymorphicSparsemaxCompositionTheorem
    +-- depends on: RecurrentPrefixMonoidHomomorphism, S4PlusS5RecurrentScanTheorem
46. ContinuousStationaryMarkovWalrasianData
47. DirectProductFiniteAutomatonComposition
48. OffPolicyFunctionApproximationStabilityBoundary
    +-- depends on: ContinuousLeftInverseTheorem
49. MarkovStationaryWalrasianCompositionTheorem
    +-- depends on: RecurrentAssociativeScanTheorem, ContinuousLeftInverseTheorem, ContinuousStationaryMarkovWalrasianData, DirectProductFiniteAutomatonComposition, OffPolicyFunctionApproximationStabilityBoundary
50. ExactReconstructionOnImage
51. GlobalConjugacyEquivalence
52. GeneralizedWalrasianEquilibrium
    +-- depends on: ContinuousStationaryMarkovWalrasianData
53. ConjugateWalrasianTransport
    +-- depends on: ContinuousStationaryMarkovWalrasianData, ExactReconstructionOnImage, GeneralizedWalrasianEquilibrium
54. BairdSevenStarProblem
55. NonIIDMarkovWalrasianProblem
    +-- depends on: ContinuousStationaryMarkovWalrasianData
56. Majority3ShapleyEquilibrium
57. CanonicalGlobalTokenConjugacyTheorem
58. FiniteFunctionExactIsomorphismTransportTheorem
    +-- depends on: StateIsomorphism
59. FiniteRecurrentFunctionExactTranslationTheorem
    +-- depends on: StateIsomorphism, FiniteFunctionExactIsomorphismTransportTheorem
60. FinitePOMDPExactTransport
    +-- depends on: StateIsomorphism
61. ArchitecturePreservingCanonicalRNNLMIsomorphism
    +-- depends on: StateIsomorphism
62. CanonicalExactRNNLMTheorem
    +-- depends on: CanonicalGlobalTokenConjugacyTheorem
63. CanonicalGlobalTokenLMCompositionTheorem
    +-- depends on: RecurrentPrefixMonoidHomomorphism, CanonicalGlobalTokenConjugacyTheorem
64. CanonicalIntegerHaarScaledOrthogonalityTheorem
65. CanonicalAStarCostGuidanceTheorem
66. CanonicalFullStateHaarSparsemaxInvariantCompositionTheorem
67. CanonicalHaarSparsemaxFullStateClosureTheorem
68. CanonicalLinearHaarSparsemaxAttentionCompositionTheorem
69. CanonicalFiniteCycleExclusionIsomorphismTheorem
    +-- depends on: StateIsomorphism
70. CanonicalOperatorCompositionTheorem
71. CanonicalBoundedFactorLiftTheorem
72. FiniteFactorRecurrenceWithoutStateRecurrenceTheorem
73. CanonicalEndogenousObservationBoundaryTheorem
74. CanonicalEndogenousTopologicalObservationBoundaryTheorem
    +-- depends on: CanonicalFullLearnerConnectedScanConjugacyTheorem, CanonicalFiniteCycleExclusionIsomorphismTheorem, CanonicalEndogenousObservationBoundaryTheorem
75. CanonicalPureNonOrangeBypassCompletionTheorem
    +-- depends on: RecurrentPrefixMonoidHomomorphism, CanonicalFullLearnerConnectedScanConjugacyTheorem, CanonicalExactCompositionTuringCompletenessContract, CanonicalHaarSparsemaxFullStateClosureTheorem, CanonicalFiniteCycleExclusionIsomorphismTheorem, CanonicalOperatorCompositionTheorem, CanonicalBoundedFactorLiftTheorem, FiniteFactorRecurrenceWithoutStateRecurrenceTheorem, CanonicalEndogenousObservationBoundaryTheorem, CanonicalEndogenousTopologicalObservationBoundaryTheorem, CanonicalFiniteObservationInformationBoundaryTheorem
76. CanonicalFiniteObservationInformationBoundaryTheorem
    +-- depends on: DiscreteExactUniversalUAP
77. CanonicalExactTuringBoundaryMixtureTheorem
    +-- depends on: CanonicalExactCompositionTuringCompletenessContract, CanonicalFiniteObservationInformationBoundaryTheorem
78. CanonicalGlobalInt8LeftInverseImpossibilityTheorem
79. FiniteObservationStationaryLimitTheorem
80. CanonicalPersistentExcitationRequirementTheorem
81. ExactContractComputabilityBoundaryTheorem
    +-- depends on: CanonicalExactCompositionTuringCompletenessContract
82. CanonicalFiniteObservationStationarySubcompositionTheorem
    +-- depends on: FiniteObservationStationaryLimitTheorem
83. CanonicalClockObservationSubcompositionTheorem
    +-- depends on: CanonicalGlobalInt8LeftInverseImpossibilityTheorem
84. CanonicalBoundednessPEBoundarySubcompositionTheorem
    +-- depends on: CanonicalBoundedFactorLiftTheorem, CanonicalPersistentExcitationRequirementTheorem
85. FiniteProbabilityMass
86. FiniteProbabilityMassSemanticsTheorem
    +-- depends on: StateIsomorphism, FiniteProbabilityMass
87. FinitePOMDPProbabilitySemantics
    +-- depends on: FiniteProbabilityMass
88. FinitePOMDPProbabilitySemanticsTheorem
    +-- depends on: StateIsomorphism, FinitePOMDPProbabilitySemantics
89. FiniteBeliefUpdateExactTransportTheorem
    +-- depends on: StateIsomorphism
90. CanonicalEndogenousPOMDPObservationBoundaryTheorem
    +-- depends on: CanonicalEndogenousObservationBoundaryTheorem, FinitePOMDPProbabilitySemanticsTheorem, FiniteBeliefUpdateExactTransportTheorem
91. CanonicalExactRNNLMCapabilitySubcompositionTheorem
    +-- depends on: ArchitecturePreservingCanonicalRNNLMIsomorphism, CanonicalExactRNNLMTheorem, CanonicalGlobalTokenLMCompositionTheorem, CanonicalEndogenousTopologicalObservationBoundaryTheorem
92. CanonicalExactRNNLMObservationSubcompositionTheorem
    +-- depends on: CanonicalExactRNNLMTheorem, CanonicalEndogenousObservationBoundaryTheorem, CanonicalFiniteObservationInformationBoundaryTheorem, ExactContractComputabilityBoundaryTheorem
93. CanonicalExactRNNLMObservationTopologyCapabilityTheorem
    +-- depends on: CanonicalEndogenousTopologicalObservationBoundaryTheorem, CanonicalFiniteObservationInformationBoundaryTheorem, CanonicalExactRNNLMCapabilitySubcompositionTheorem, CanonicalExactRNNLMObservationSubcompositionTheorem
94. CanonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem
    +-- depends on: CanonicalFiniteObservationInformationBoundaryTheorem, CanonicalEndogenousPOMDPObservationBoundaryTheorem, CanonicalExactRNNLMObservationTopologyCapabilityTheorem
95. CanonicalTokenVocabularyUpperBoundTheorem
```

The direction is:

```
record A
  |
  +-- depends on --> record B
```

A composite record therefore points toward the record surfaces it packages or assumes.

## Emergent endogenous closure

The newest higher-order endogenous closure is:

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

This is an emergent composition of already declared exact surfaces, not a new primitive axiom. Its significance is the exposed cross-domain closure between exact RNN-LM capability, endogenous observation topology, finite information limits, and finite POMDP probability and belief transport.

## Exact vocabulary capacity

The canonical token carrier is exactly:

```
CanonicalToken = Fin 256
CanonicalToken <-> Int8
```

The encode and decode maps are exact inverses. Therefore this formulation has exactly 256 distinct token symbols.

For exactly `n` tokens, the sequence space has:

```
256^n
```

Across all finite lengths, the set of finite token sequences is countably infinite. That does not enlarge the vocabulary; the alphabet remains exactly 256 symbols.

The logit vector is:

```
CanonicalToken -> Int8
```

so one unconstrained Int8 logit vector has `256^256` possible coordinate assignments. That is an output-vector state-space count, not a vocabulary size and not a parameter-count estimate.

`CanonicalTokenVocabularyUpperBoundTheorem` proves the exact carrier equivalence and inverse encode/decode laws. A separate numeric cardinality theorem would be a different formal statement.

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

An e-graph extraction is never treated as a proof.

The repository does not obtain a green gate by weakening a theorem, replacing a missing proof with a trivial proposition, changing a carrier to make a theorem fit, or silently changing the semantic target.

The finite probability and POMDP layers are exact finite semantics, not full measure-theoretic probability.

The RNN-LM layers are exact formal capability and transport statements, not empirical language-model performance claims.

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


## Scheduled commit-totality README refresh

The repository now has a slow, deterministic README refresher. The Dhall surface renders the updater script; the Nix flake exposes it as `slow-readme-update`; and the scheduled GitHub workflow runs it weekly against the default branch. The updater records every commit since the previous processed commit rather than sampling an arbitrary recent window. Dhall is used as the declarative text-generation layer, while Nix supplies the reproducible runtime.

<!-- BEGIN RECENT COMMIT TOTALITY -->
last-processed-commit: 091ee6eca250e9a6505f6793b0c3fdfb7f45f1d6
unprocessed-commit-count: 0

The next scheduled run will account for every commit after this bootstrap point.
<!-- END RECENT COMMIT TOTALITY -->

## Strict neural-function-class separation

The strict separation graph is intentionally a graph of one object only: the full connected composition. It does not treat attention, Haar orthogonality, recurrence, factor recurrence, optimizer coupling, or observation topology as separate function-class wins.

The canonical path is:

```
F_base
  -> CanonicalFullLearnerConnectedScanConjugacyTheorem
  -> CanonicalHaarSparsemaxFullStateClosureTheorem
  -> CanonicalBoundedFactorLiftTheorem
  -> FiniteFactorRecurrenceWithoutStateRecurrenceTheorem
  -> CanonicalEndogenousObservationBoundaryTheorem
  -> CanonicalEndogenousTopologicalObservationBoundaryTheorem
  -> CanonicalFiniteObservationInformationBoundaryTheorem
  -> CanonicalExactRNNLMObservationTopologyCapabilityTheorem
  -> CanonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem
  -> F_full_connected
```

The component theorems remain valid Agda surfaces, but the separation graph promotes them into composed surfaces rather than giving them independent separation status. S4PlusS5RecurrentScanTheorem is present on the theorem surface and is absorbed into the connected learner/scan composition; the full learner theorem also exposes the exact Watkins target flow through the recurrent and F4/L2 optimizer steps.

A strict result still requires all three semantic obligations: the baseline must embed into the full connected class, a concrete function must be constructed through the entire path, and a canonical Agda theorem must prove that witness is not representable by the baseline. The repository currently has the connected composition and the factor-recurrence mechanism, but it does not yet have that nonrepresentability witness. Therefore the graph remains NOT_ESTABLISHED.

### Factor recurrence, Nat algebra, regularization, and generalization

A useful mathematical schema is:

```
(Nat,+,·)
    -> regularized parameter dynamics
    -> bounded/stable factor image q(S)
    -> finite-factor recurrence
    -> optional generalization/stability bound
```

The important point is that Nat being an unbounded semiring does not itself imply recurrence. The recurrence theorem needs a separate boundedness, invariant-set, contraction, quotient-finiteness, or equivalent certificate on the observed factor. A regularizer can be a candidate source of that certificate, but only after its actual objective is connected to a trajectory bound or stability inequality.

For example, if a regularized update can be proved to satisfy a factor contraction such as

```
d_F(q(T_theta(s)), q(T_theta(s'))) <= rho d_F(q(s), q(s'))
with rho < 1,
```

then a finite/invariant factor space can yield eventual recurrence. A separate stability or complexity argument can then address generalization; recurrence alone is not a generalization guarantee. Empirical/theoretical literature supports the broader separation between recurrent stability, regularization, and overfitting/generalization rather than identifying them as the same theorem.

This relationship is recorded as a candidate in .ci/discovery/neural-function-class-separation-graph.json; it is not promoted to an Agda theorem until the repository has an explicit regularizer, factor map, and quantitative certificate.
