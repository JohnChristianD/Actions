# Meta-Search Architecture

The canonical automated discovery layer is now novel learner-theorem basis search.

Mercury enumerates a small typed grammar of transformations and theorem relations, quotients candidates with an equivalence-class layer, removes candidates already represented in the canonical theorem source, and emits only the remaining nontrivial basis candidates. Agda then checks the generated propositions with --safe.

The search object is a theorem about the executable learner. The search procedure is not a theorem subject and does not attempt to prove its own self-consistency.

## Roles

| Layer | Role |
|---|---|
| Agda | Executable learner semantics, exact finite evaluation, theorem checking, and final certificate gate |
| Mercury | Typed theorem-program enumeration, reusable equivalence quotienting, novelty pruning, and generated-candidate emission |
| Guix/Guile | Reproducible orchestration and tool pinning |
| Manual source | Learner parameters, imports, carriers, and formal assumptions remain explicit |

## Current discovery grammar

The raw finite basis contains two actual learner transformations:

- NormPair replacement.
- Period-4 clock replacement.

It considers observable-invariance relations over:

- NormPair replacement and the count-step observable;
- NormPair replacement and the Q-log-step observable;
- period-4 clock replacement and the endogenous-feedback observable;
- period-4 clock replacement and the Watkins-target observable.

Each relation also has an iterate form in the raw grammar. The Mercury equivalence quotient collapses those downstream forms into the one-step basis.

The current basis candidates are:

- count-step is invariant under NormPair replacement;
- Q-log-step is invariant under NormPair replacement;
- endogenous feedback is invariant under the period-4 clock replacement;
- Watkins target is invariant under the period-4 clock replacement.

The generated proofs are compositional. They use existing canonical laws through congruence/transitivity rather than emitting bare reflexivity proofs.

These are not already named in TheoremsMonolith.agda at discovery time. The Mercury generator also scans the canonical theorem source and removes any candidate whose declaration is already present.

## Discovery loop

The active loop is:

    typed learner transformation
        ->
    typed theorem relation
        ->
    equivalence quotient
        ->
    source-level novelty guard
        ->
    generated Agda proposition
        ->
    agda --safe
        ->
    accepted or rejected theorem candidate

This separates novelty selection from proof acceptance. A candidate is not considered discovered merely because Mercury emitted it. It must pass the Agda proof gate.

## Why use an equivalence quotient

The discovery space contains many statements that are consequences of stronger statements. For example, if a transformation commutes with the one-step learner transition, the corresponding iterate-commutation family is structurally downstream.

The Mercury quotient therefore keeps a smaller basis rather than emitting every syntactic consequence. This is the current lightweight e-graph boundary: Mercury uses equivalence classes to quotient theorem programs before proof generation. A full equality-saturation e-graph is not justified yet because the current grammar is finite and the quotient rules are explicit.

That makes Mercury the right host for the discovery layer without introducing another runtime or trust boundary. The semantic boundary remains the Agda learner. Mercury is only reducing redundant theorem search.

## What was pruned

The following were removed from the canonical discovery path because they were already included or were search machinery rather than novel learner theorems:

- Finite compositions of attention/NormPair/optimizer replacements already covered by canonicalPolicy-learnerReplacement-composition.
- Repeated preservation forms already covered by the canonical iterate lemmas.
- The old TSTS composition generator.
- Generic list/sign involution testing.
- PVS.
- JAxtar A*/Q*.
- Evolutionary-population proposal layers.

The existing FiniteTSTSEndogenousConnectedTheorem remains a theorem surface, but it is no longer used as the semantic target of theorem discovery.

## What counts as a novel candidate

A discovery candidate must:

1. act on an actual learner state or learner-derived observable;
2. express a nontrivial relation such as invariance, equivariance, commuting, quotient preservation, or an analogous structural law;
3. not already be represented in the canonical theorem source;
4. survive the Mercury equivalence quotient;
5. produce an Agda proposition accepted by agda --safe.

External reward, search regret, or architecture labels are not theorem semantics.

## Search policy boundary

No particular search policy is canonical here.

For the current finite grammar, enumeration plus quotienting is exact and auditable. A future larger grammar can replace enumeration with best-first, A*, CEGIS, or another search policy without changing the theorem language or proof gate.

That is the intended division:

    theorem grammar = semantic contract
    Mercury        = candidate engine
    search policy  = replaceable implementation detail
    Agda           = authority

## Runtime boundary

No external JAX/TensorFlow search runtime is imported into the canonical source path. The current system keeps the formal learner small, finite, and directly checkable.

Mercury remains outside the Agda kernel trust boundary. Mercury proposes candidate propositions; Agda decides whether the generated theorem is actually proven.

## Hash-consed e-graph

The canonical discovery engine now uses `.ci/discovery/symbolic_egraph.m` for a real ground e-graph core:

- general enodes with arbitrary symbol names and child e-class IDs;
- hash-consing through Mercury's versioned hash-table implementation;
- union-find e-class representatives;
- rebuild-based congruence closure after merges;
- declarative ground rewrite equations;
- cost-based representative extraction.

`learner_theorem_egraph.m` maps typed learner laws into these enodes and applies the theorem rewrite registry before minimal extraction. The generic regression test explicitly merges `a` and `b` and checks that `f(a)` and `f(b)` become equivalent by congruence closure.

This is now a reusable symbolic engine rather than an `eqvclass`-only quotient.

## Exact recurrent scan theorem class

`CanonicalLearnerMonolith.agda` now defines `Endomorphism`, exact recurrent-prefix endomorphisms, a `Nat`-indexed stream scan, and a split-prefix theorem. `TheoremsMonolith.agda` packages these as `RecurrentAssociativeScanTheorem`.

The theorem does not assume a bounded sequence length. For arbitrary natural `m` and `n`, the prefix of length `m + n` is exactly the `m` prefix followed by the `n`-length scan of the shifted stream.

The canonical GRU instantiation is `canonicalGRU-recurrent-associative-scan-theorem`.

A separate theorem, `int8-no-countably-unbounded-injective`, proves that an `Int8` state cannot injectively encode an unbounded `Nat` index. Thus the exact scan theorem solves the algebraic/parallel-evaluation side of long-horizon recurrence, while the finite-state theorem establishes the formal information-capacity limit for lossless unbounded history.

## Reservoir-computing theorem correspondence

The repository also contains `FiniteReservoirFaithfulnessTheorem`, the exact finite/discrete proof object:

`left inverse -> injective observation -> exact readout factorization`.

This is the discrete theorem boundary used for comparison with Sugiura et al.'s 2025 result on reservoir universality. The external theorem is stronger and analytically different: in its continuous setting, universality, neighborhood separation, and existence of a uniformly continuous inverse are equivalent. The repository does not claim that its finite Int8 learner satisfies those continuous assumptions.
