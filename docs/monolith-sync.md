# Monolith / theorem / e-graph sync

## Canonical ownership

- Learner semantics: `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`.
- Public theorem facade: `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`.
- `TheoremsMonolith/Part1a` … `Part5`: dependency-ordered CI compilation partitions only.
- Mercury: discovery/equality-saturation layer; it does not define learner semantics.

## Current composed theorem target

Mercury does not force a named theorem target. It derives maximal dependency paths from every non-reflexive declaration in `TheoremsMonolith.agda`, inserts those paths into the e-graph, saturates, analyzes, and extracts them. The current exact theorem surfaces include:

1. `canonical-integer-haar-scaled-orthogonality-theorem`: integer/scaled two-point Haar cross-orthogonality plus energy;
2. `canonical-a-star-cost-guidance-theorem`: exact zero-cost, successor-cost, and token-trace composition laws;
3. `canonical-linear-haar-sparsemax-attention-composition-theorem`: integer Haar sum/difference composed with the existing sparsemax head;
4. `canonical-full-state-haar-sparsemax-invariant-composition-theorem`: Haar/sparsemax attention invariance under the existing NormPair and optimizer replacement seams;
5. `canonical-haar-sparsemax-full-state-closure-theorem`: closes the integer Haar linearity, fixed sparsemax counts, and full-state learner-replacement invariance into one Agda-safe composition surface;
6. `canonical-learner-replacement-closure-theorem`: closes policy invariance under an arbitrary finite list of existing NormPair/optimizer replacements;
7. the broader recurrent-prefix, finite-product, exact-readout, and stationary-Walrasian composition surfaces already present in the monolith.

8. `RecurrentScanConjugacyTheorem` / `canonical-recurrent-scan-conjugacy-theorem`: local transition conjugacy lifts exactly to every recurrent prefix, giving a representation-independent scan closure law.

Agda `--safe` is authoritative. Mercury extracts the canonical theorem monolith, builds the dependency graph, performs A* cost-guided path search, inserts source laws and graph plans into the e-graph, saturates sound rewrite relations, rebuilds, analyzes e-classes, and extracts costed representatives. It does not prove the Agda induction or invent semantic laws.

## Sparsity boundary

For weights (w_i), let (S = Σ_i w_i), (Q = Σ_i w_i^2), action count (d), and support (k). The exact hard support sparsity is (1-k/d). The exact Tsallis-2 effective-support sparsity is (1-S^2/(dQ)=(dQ-S^2)/(dQ)), with zero-vector convention 1. The hard measure is the uniform-on-support boundary of the Tsallis-2 measure; the current theorem surface records the general algebraic representation and the uniform-support boundary condition.

The canonical learner's policy is still a two-action sparsemax specialization. Generalizing the measure does not silently change that executable policy type.

## CI handoff

The learner job produces Agda interfaces. Each theorem partition downloads the complete predecessor interface closure and hides predecessor source files before checking the current partition. This prevents repeated learner recompilation while retaining kernel-checked interfaces. Mercury remains a separate Nix stack.

## F4 history invariant

The recent F4 history was inspected. The current canonical F4 state is `F4IntUState` with five `Int8` fields, and its theta step consumes `canonicalWatkinsTarget` with global L2 correction. The older six-coordinate coupled F4 design and legacy hardsign variants are historical code paths, not current canonical semantics. `lcbNegate` and `int8Neg` are definitionally the same modular negation; deduplication can be done without changing the F4 semantic flow.

## 2026-09-21 graph-hypothesis sync

The former empirical README representation hypotheses were not source-derived theorem laws and were removed from the canonical claim surface. The replacement hypothesis set is exactly two source-derived theorem hypotheses: the integer Haar orthogonality certificate and the A* cost-guidance certificate. The existing Haar/sparsemax composition certificates remain downstream composition surfaces, not additional new hypotheses. The distinction is deliberate: Mercury discovers dependency paths; only Agda `--safe` turns a source declaration into a proof.

The methodology reference for this pass is Scott N. Walck, *Learn Physics with Functional Programming: A Hands-on Guide to Exploring Physics with Haskell* (No Starch Press, 2023, ISBN-13 9781718501669). It is used as a typed-functional-programming modeling reference, not as evidence for the learner's theorem claims.


9. `CanonicalFullLearnerConnectedScanConjugacyTheorem`: the full learner's local transition conjugacy lifts to arbitrary iteration depth while retaining the existing GRU/F4/Norm connected-coupling bridge.

## 2026-09-22 endogenous scan-conjugacy / exact Turing boundary

10. canonical-full-learner-connected-scan-conjugacy-theorem is now explicitly full-state in scope: its scan law ranges over the exact CanonicalFullLearnerState, while its coupling certificate exposes Watkins state projection, exact modified-Watkins target identity, and target consumption by both the GRU and F4/L2 paths. The GRU/F4/Norm connected bridge remains the existing exact bridge.

The autonomous iterateCanonical scan is deliberately kept separate from arbitrary input-prefix scans. The former is generated by powers of canonicalFullStep; the latter is generated by the input-indexed recurrent transition family. A time-iterate conjugacy does not silently imply arbitrary prefix-word conjugacy.

The proposed exact Turing-completeness record was repaired into a contract plus canonicalExactCompositionTuringCompletenessContract-impossible. The obstruction is endogenous: the exact canonicalFullStep is fixed-point-free because its clock increments, so the contract's universal exact step simulation fails already on the self-loop two-counter machine. No weaker precision, extra input stream, or substitute architecture was introduced.

Knowledge delta: the canonical theorem/docs now record the distinction between autonomous scan conjugacy and input-prefix conjugacy, explicit modified-Watkins full coupling, and the exact obstruction to the proposed Turing-completeness contract.
## Bounded-factor completion

The active theorem facade now owns the exact bounded-factor / injective-lift layer:

- `canonicalF4ThetaQ-bounded` — every exact F4 theta representation remains in `Fin 256`.
- `canonicalF4ThetaQ-not-orbit-injective` — the finite F4 factor cannot injectively encode the unbounded Nat orbit index.
- `canonicalF4-factor-collision-separates-full-state` — a repeated F4 representation can occur only at distinct full exact states, because the canonical clock makes the full orbit index-injective.
- `canonical-bounded-factor-lift-theorem` — packages the three facts as one theorem surface.

The finite-carrier witness is now proved directly in `TheoremsMonolith.agda`; `FiniteUniversalBoundary.agda` is therefore retired. The legacy F4/finite-cycle/operator modules that depended on the superseded learner surface were pruned from the canonical branch. Benchmark/game-port modules remain separate where they carry distinct environment semantics rather than duplicate learner proof semantics.

## Non-orange-bypass theorem graph

```text
T1  CanonicalAQLoopTheorem
        |
        v
T2  canonicalFullStep / exact shared signal coupling
        |
        v
T3  canonicalClockAfter + canonicalOrbit-state-injective
        |
        +------------------------------+
        |                              |
        v                              v
T4  recurrent-prefix monoid       T5  Haar/sparsemax replacement closure
        |                              |
        +---------------+--------------+
                        v
T6  exact finite Int8 F4 representation
        |
        v
T7  canonicalF4ThetaQ-bounded
        |
        v
T8  pigeonhole finite-factor collision
        |
        v
T9  canonicalF4-factor-collision-separates-full-state
        |
        v
T10 repeated F4 representation != repeated full exact state
        |
        v
T11 exact computational boundary / no exact two-counter contract
```

The graph is deliberately directional: no finite F4 factor is promoted to a full-state inverse, no L2 contraction is assumed, and no e-graph/A* candidate is treated as an Agda proof. The finite collision is discharged at the exact `Fin 256` representation boundary, while full-state separation comes from the independently proved clock-growth injectivity.

## Lyapunov / cycle / operator distinction

The canonical theorem surface already proves exact finite-cycle exclusion and generic state-isomorphism/conjugacy transport. Those are transition-semantic theorems: they follow from exact iteration and the clock-growth law. The repository does not currently expose a theorem named or typed as a Lyapunov function with a descent condition such as `V (step s) < V s`, nor does the existing `canonicalIntegerHaarEnergy` constitute such a Lyapunov certificate; it is an exact integer Haar energy identity.

The operator-composition result is likewise already present through the canonical `Endomorphism` composition algebra. `CanonicalOperatorCompositionTheorem` now packages identity, composition, and associativity in the theorem monolith, so the standalone connected-operator-composition module is semantically redundant and has been removed. The new endogenous result remains the bounded-factor/injective-lift theorem: finite F4 recurrence is separated from full-state recurrence by exact clock injectivity.


## Emergent factor-recurrence separation

The active theorem surface now includes `FiniteFactorRecurrenceWithoutStateRecurrenceTheorem` and `canonical-finite-factor-recurrence-without-state-recurrence`. It states the endogenous representation boundary explicitly: any orbit observed through `Fin 256` has two distinct time indices with equal factor value, while an injective exact orbit keeps the corresponding full states distinct. This is a finite-factor/aperiodic-orbit separation result; it is not a Lyapunov descent theorem and does not assert that the F4 update is contractive.

`CanonicalPureNonOrangeBypassCompletionTheorem` is the pre-graphed monolith endpoint. It packages the recurrent-prefix monoid law, full-learner scan conjugacy, exact Turing-boundary contract, Haar/sparsemax closure, finite-cycle isomorphism transport, operator composition, bounded-factor lift, and the new factor-recurrence separation theorem without introducing a second proof surface.

The remaining `FullCoupled/*.agda` files outside the two monoliths are intentionally retained because they provide distinct game/environment benchmark semantics or the signed-divisibility arithmetic bridge. They are not semantically redundant theorem facades.


## Deeper endogenous information boundary

The theorem graph now exposes `CanonicalFiniteObservationInformationBoundaryTheorem`. It composes four already-canonical facts: the full canonical orbit is Nat-index injective; every `Fin 256` factor recurs; an exact `Int8` observation cannot have a left inverse on the full canonical orbit; and universal exact discrete UAP through such an observation is impossible. This is stronger than merely saying a finite factor recurs: it identifies the precise information-preservation boundary created by the finite observation carrier.

This does not assert that every finite observation is useless for every target. It rules out exact left-invertible observation of the entire unbounded canonical orbit through `Int8`, and therefore rules out universal exact readout through that observation.

## 2026-09-22 pre-graphed theorem completion gate

The semantic-contract gate now requires the bounded-factor lift, finite-cycle isomorphism transport, operator composition, and finite-observation information-boundary theorem surfaces before the pure non-orange-bypass endpoint is accepted. These are graph endpoints over existing monolith declarations, not parallel proof modules.

The four historical working branches are synchronized to the same canonical main commit after this gate update. Their refs remain only as names; they carry no divergent content.

## Branch consolidation

`main` is the canonical integrated head. The three divergent branch heads were audited against their merge bases. Their meaningful additions were already represented in the canonical CI/Dhall surface or were retained as the Econlib stationary-Markov graph documentation. No branch-specific Agda theorem surface remains outside the two monoliths.

## 2026-09-22 clock/Lyapunov and exact-computability boundary

The Nat clock is now recorded as a separate semantic axis from Lyapunov-style energy arguments. Exact clock growth gives temporal index separation and excludes finite cycles; it does not assert descent, boundedness, or convergence. The finite-observation theorem records the complementary fact that an exact unbounded time index cannot be recovered injectively through a finite Int8 observation.

The exact Turing boundary is expressed as a contract mixture: the repository rules out the specified exact autonomous one-step two-counter simulation while retaining the exact Nat clock and finite-observation boundary. This is not a claim that every weaker computational-completeness notion is impossible; any future positive construction must explicitly relax at least one contract component.


## 2026-09-22 explicit global inverse, stationary-limit, and PE boundary

The finite-observation information boundary is now stated with an explicit global quantifier: for any fixed canonical kernel and initial state, no observe : CanonicalFullLearnerState → Int8 has a global inverse : Int8 → CanonicalFullLearnerState satisfying inverse (observe s) ≡ s for every canonical state. The Nat-clock orbit supplies the finite-carrier contradiction, while the conclusion itself is global.

A monotone Lyapunov observable plus boundedness is not being promoted to a stationary-distribution convergence theorem. The new MonotoneConvergenceToStationaryDistributionTheorem explicitly requires the transition law, a monotone Lyapunov quantity, a convergence notion, and preservation of the limit by the transition operator. This keeps the stochastic limit step separate from the optimizer's existing boundedness result.

Persistent excitation is likewise recorded as a separate requirement. The current canonical Agda surface does not contain the matrix/Gramian probability or adaptive-identification machinery needed for a genuine PE proof. Therefore the new theorem surface is a contract boundary, not a fake PE proof: bounded Int8 representation is not silently treated as PE.

The exact Turing-completeness obstruction remains contract-specific. It does not generalize automatically to every computational function class; the decisive assumptions are the specified exact autonomous clock and finite observation/contract structure.


## 2026-09-22 graph-search completion: four requirements and three subcompositions

The graph-search layer now has four explicit required theorem nodes: global Int8 left-inverse impossibility, the monotone-energy/stationary-distribution convergence contract, persistent-excitation requirement, and exact-contract computability boundary. It also has three explicit subcomposition nodes: exact clock plus finite-observation information loss, monotone energy plus stationary-limit preservation, and bounded-factor plus PE boundary.

These are dependency-graph obligations, not hidden implications. In particular, the monotone-energy composition preserves its convergence and limit-preservation assumptions, and the PE composition preserves PE as an independent information condition. Mercury/A* discovers paths; Agda --safe remains proof authority.


## 2026-09-22 emergent endogenous observation boundary

The canonical theorem facade now exposes `CanonicalEndogenousObservationBoundaryTheorem`. It composes exact Nat-clock orbit embedding, finite Int8 observation recurrence, explicit global left-inverse impossibility, and exact endogenous Watkins-target readout under a hypothetical left inverse. The result is a genuine information boundary: exact endogenous target readout is available conditional on exact state recovery, while the finite Int8 observation cannot supply that global recovery. This does not claim that the Watkins target itself is unrecoverable from every finite feature; it rules out global state recovery through the specified Int8 observation.

The Mercury graph-search layer now also has an explicit A* plan query for `CanonicalMonotoneEnergyStationarySubcompositionTheorem`, and the theorem e-graph gate requires that plan to be found. The monotone-energy node remains a contract surface: monotone energy, trajectory convergence, and limit preservation are explicit assumptions; boundedness alone is not silently converted into stationary-distribution convergence. This matches standard Foster-Lyapunov usage, where additional drift/recurrence conditions are needed for stationary conclusions.


The endogenous boundary is also an explicit A* graph-search target: `CanonicalEndogenousObservationBoundaryTheorem` must have a dependency plan before the sync gate passes. This keeps the new result discoverable rather than merely present in the Agda monolith.


## 2026-09-22 Lyapunov-free stationary graph seam and endogenous topology

The graph-search stationary convergence path uses the Lyapunov-free `FiniteObservationStationaryLimitTheorem`: transition law, trajectory convergence, and limit preservation are explicit. The canonical proof surface therefore carries no standalone Lyapunov theorem or Lyapunov stationary subcomposition. Exact clock growth, finite-cycle exclusion, and finite-factor recurrence are retained directly because they are temporal/finite-carrier facts rather than descent arguments.

The new CanonicalEndogenousTopologicalObservationBoundaryTheorem composes the existing full-learner scan-conjugacy theorem, finite-cycle/isomorphism transport, and the endogenous observation boundary. Its content is compositional rather than a new axiom: topology preserves the exact scan/cycle structure while the finite observation still cannot provide a global exact state inverse. The endogenous Watkins target remains exactly state-dependent; conditional exact readout under a hypothetical inverse therefore does not imply that the finite observation can recover the target globally.

Watkins-Dayan is used only as the RL comparison boundary: classical Q-learning convergence is a tabular/asymptotic result with repeated state-action visitation and stochastic-approximation conditions. A recurrent function-approximating learner should not inherit that conclusion merely from sharing a Watkins-style target. The canonical monolith instead exposes the exact endogenous target coupling and separately proves the finite-observation information boundary.

Lyapunov-style theorems are therefore no longer needed for the topology, finite-cycle, observation-injectivity, recurrent-prefix, or exact-computability results already present. They remain appropriate only where the intended conclusion is genuinely a stability/drift/boundedness/convergence claim that cannot be discharged by exact topology, fixed-point semantics, or a direct finite-state Markov argument.

## 2026-09-22 minimal probability semantics and endogenous POMDP seam

The canonical theorem monolith now carries a minimal exact finite probability semantics without importing a second analytic arithmetic tower. `FiniteProbabilityMass` stores Nat weights, a positive denominator, and an exact normalization proof; the coordinate probability is represented by the exact weight/denominator pair. `FiniteProbabilityMassSemanticsTheorem` transports those masses through exact finite state isomorphisms pointwise.

`FinitePOMDPProbabilitySemanticsTheorem` packages normalized transition and observation kernels with the existing Int8 reward channel. It is deliberately a semantics seam, not a belief-state update or stochastic convergence theorem. The new `CanonicalEndogenousPOMDPObservationBoundaryTheorem` composes that probability seam with the existing endogenous observation boundary, so the graph now surfaces the probabilistic endogenous composition automatically.

No Lyapunov theorem is required by this path.

## 2026-09-22 exact RNN-LM graph promotion candidates

The exact RNN-LM surface was already present but was not fully promoted into the theorem graph gate. The graph now requires CanonicalGlobalTokenConjugacyTheorem, CanonicalGlobalTokenLMCompositionTheorem, CanonicalExactRNNLMTheorem, and ArchitecturePreservingCanonicalRNNLMIsomorphism.

Two theoremized subcompositions are also pre-graphed:

1. CanonicalExactRNNLMCapabilitySubcompositionTheorem packages the exact token-model theorem, global token-LM composition, architecture-preserving transport, and the endogenous topological observation boundary.
2. CanonicalExactRNNLMObservationSubcompositionTheorem packages the exact RNN-LM theorem with endogenous observation, finite-information, and exact-computability boundaries.

These are promotion candidates, not replacements for the canonical learner. Mercury/A* must first recover their dependency paths; Agda --safe remains the proof authority. They are deliberately sequence-model capability surfaces, not a claim that the current executable policy is a general unconstrained language model.

The topology theorem is now useful as a real dependency rather than documentation-only: the first RNN-LM capability subcomposition depends on CanonicalEndogenousTopologicalObservationBoundaryTheorem, which itself transports exact scan/cycle structure while retaining the finite-observation information boundary.

## 2026-09-22 MarkovStationary Walrasian source correction

The Walrasian node is tied to the upstream Lean EconlibExamples/Equilibrium/MarkovStationary.lean composition, not a generic invented stationary-Walrasian theorem. The local MarkovStationaryWalrasianCompositionTheorem remains a graph node and is now required by theorem search. The upstream example is a concrete witness for its specified economy; it should not be silently promoted to a general equilibrium-existence theorem. The cross-repository CI lane already checks the upstream Economy.WalrasianEquilibrium, Economy.exists_equilibrium, and MarkovStationary surfaces before accepting the adapter graph.

## 2026-09-22 exact RNN-LM observation/topology and vocabulary closure

The theorem graph now includes an endogenous exact RNN-LM observation/topology capability closure. Its intended dependency path is exact RNN-LM semantics → architecture-preserving token transport → endogenous observation boundary → endogenous topological boundary → finite-observation information boundary.

The graph also includes CanonicalTokenVocabularyUpperBoundTheorem. The canonical token encoder/decoder are exact inverses against Int8, so this is an exact finite-cardinality boundary for the canonical token carrier, not a statistical estimate of real-world language-model vocabulary size.

Both are promotion candidates until Agda --safe and the Mercury dependency graph type-check them.
