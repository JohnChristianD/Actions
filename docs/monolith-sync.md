# Monolith / theorem / e-graph sync

## Canonical ownership

- Learner semantics: `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`.
- Public theorem facade: `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`.
- `TheoremsMonolith/Part1a` … `Part5`: dependency-ordered CI compilation partitions only.
- Mercury: discovery/equality-saturation layer; it does not define learner semantics.

## Current composed theorem target

Mercury forces `canonical-endogenous-sparse-summary-egraph-theorem`. Its Agda certificate composes:

1. sparsemax attention → endogenous Watkins target → GRU/F4 mediator;
2. exact recurrent endomorphism summary/compression scan;
3. prediction sufficiency of a sound decoder;
4. general finite-action Tsallis-2 near-sparsity over `Fin d -> Nat`;
5. an exact support-parameterized prefix work model.

Agda `--safe` is authoritative. Mercury extracts the theorem partitions, builds an e-graph, saturates sound rewrite relations, rebuilds, analyzes e-classes, and extracts a costed representative. It does not prove the Agda induction or invent semantic laws.

## Sparsity boundary

For weights (w_i), let (S = Σ_i w_i), (Q = Σ_i w_i^2), action count (d), and support (k). The exact hard support sparsity is (1-k/d). The exact Tsallis-2 effective-support sparsity is (1-S^2/(dQ)=(dQ-S^2)/(dQ)), with zero-vector convention 1. The hard measure is the uniform-on-support boundary of the Tsallis-2 measure; the current theorem surface records the general algebraic representation and the uniform-support boundary condition.

The canonical learner's policy is still a two-action sparsemax specialization. Generalizing the measure does not silently change that executable policy type.

## CI handoff

The learner job produces Agda interfaces. Each theorem partition downloads the complete predecessor interface closure and hides predecessor source files before checking the current partition. This prevents repeated learner recompilation while retaining kernel-checked interfaces. Mercury remains a separate Nix stack.

## F4 history invariant

The recent F4 history was inspected. The current canonical F4 state is `F4IntUState` with five `Int8` fields, and its theta step consumes `canonicalWatkinsTarget` with global L2 correction. The older six-coordinate coupled F4 design and legacy hardsign variants are historical code paths, not current canonical semantics. `lcbNegate` and `int8Neg` are definitionally the same modular negation; deduplication can be done without changing the F4 semantic flow.
