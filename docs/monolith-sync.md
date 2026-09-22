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
