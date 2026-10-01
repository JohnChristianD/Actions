# Agda, SMT, Vehicle, JAX, Mirth, Mercury, and Elm boundaries

## Agda authority

The learner and theorem monoliths are the only active Agda sources. The theorem monolith consumes the learner in one direction.

SMT and Vehicle remain integration boundaries. Their results do not replace accepted Agda proof terms.

## GRU left inverse and tail-stability kernel

The canonical statistical representation stores the original GRU state and decodes by first projection. The accepted left-inverse and injectivity chain is:

`canonicalGRUStatisticalDecodeEncode`
→ `canonicalGRUStatisticalEncodeLeftInverse`
→ `leftInverse-implies-injective`
→ `canonicalGRUStatisticalEncodeInjective`.

The convergence-identifiability kernel then requires explicit injectivity, exact step conjugacy, and an eventually fixed feature tail. It does not manufacture physics, economics, or Baird witnesses.

## Canonical Baird boundary

The Baird construction is concrete and learner-specific.

`CanonicalLearnerBairdSevenStarWitness K s` is parameterized by the canonical learner kernel/state. Its persistent-GRU tail is supplied by the already-proved canonical learner iterate theorem. The seven-state/eight-feature, behavior-policy, target-policy, reward, discount, feature-equation, and divergence-witness fields remain explicit.

There is no generic Baird theorem in the active surface.

## Retained sparsity surface

The L1 and 1-path-norm definitions and theorem wrappers were pruned.

The exact hard-sparsity degeneration remains through `CanonicalHardSparsityDegeneracyTheorem`.

The finite Tsallis-2 surface remains through `ActionWeights`, support/mass/square-mass definitions, the finite rational Tsallis-2 numerator/denominator construction, its zero/nonzero laws, support sparsity, and `UniformSupportTsallisBoundary`.

This is a finite constructive boundary. It does not assert unformalized continuous entropy or analytic properties.

## JAX algorithm boundary

The Python JAX execution wrapper has been removed. The theorem monolith retains `JAXExecutionMirrorReproof` as a typed Agda contract for the retained algorithms.

The retained contracts cover affine vector mapping, associative prefix execution, recurrent scan, lexicographic ordering, sparse-support algorithms, integer LayerNorm arithmetic, signed gating, GRU hidden updates, finite Tsallis-2/support sparsity, and scan-sum.

The Agda laws are the proof surface. They do not claim to reprove a JAX compiler, tracing engine, or Python runtime.

## Mirth import synchronization

The common import block is learner-owned and theorem-consumed.

The Mirth synchronizer checks exact marker cardinality, byte equality, learner-to-theorem dependency direction, canonical learner import count, and exact SMT/Z3/Vehicle imports. Predicate checks execute concurrently and aggregate all failures. Write mode is bounded by a lock and only installs a fully constructed candidate.

No separate shell synchronizer is required.

## Mirth Agda graph

The graph generator reads both monoliths and extracts top-level declarations plus source-level declaration references. Learner and theorem extraction run concurrently. Nodes and edges are deduplicated and sorted before Elm generation.

This is an exhaustive source-reference graph for the parser's declaration/reference model, not an Agda elaboration graph. Agda's accepted terms remain authoritative.

## Mercury semantic graph

Mercury remains responsible for semantic dependency and e-graph reasoning. Its curated semantic frontier should not be confused with the exhaustive Mirth source-reference graph. The two graphs answer different questions: Mercury groups semantic laws and equivalences; Mirth exposes every parser-detected source reference.

## Elm Pages

The Elm application consumes the generated graph data and exposes all generated nodes and edges dynamically. It provides declaration filtering, complete relation lists, counts, and an SVG neighborhood. This is pure Elm and does not execute Agda, Mirth, Mercury, SMT, Vehicle, or JAX.

## PPAD boundary

The repository does not claim PPAD-completeness. Fixed-point and equilibrium definitions are present, but completeness still requires the formal search relation, polynomial encoding bounds, membership, and hardness reduction.

## Toolchain discipline

Agda 2.8.0 and standard library 2.3 are pinned. No Python source files or shell-script files are part of the active source surface. Markdown remains link-free.
