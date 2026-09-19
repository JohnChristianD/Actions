# Meta-Search Architecture

The canonical automated discovery layer is now novel learner-theorem basis search.

Mercury enumerates a small typed grammar of transformations and theorem relations, quotients candidates with an equivalence-class layer, removes candidates already represented in the canonical theorem source, and emits only the remaining nontrivial basis candidates. Agda then checks the generated propositions with --safe.

The search object is a theorem about the executable learner. The search procedure is not a theorem subject and does not attempt to prove its own self-consistency.

## Roles

| Layer | Role |
|---|---|
| Agda | Executable learner semantics, exact finite evaluation, theorem checking, and final certificate gate |
| Mercury | Typed theorem-program enumeration, novelty pruning, equivalence quotienting, and generated-candidate emission |
| Guix/Guile | Reproducible orchestration and tool pinning |
| Manual source | Learner parameters, imports, carriers, and formal assumptions remain explicit |

## Current discovery grammar

The raw finite basis contains two actual learner transformations:

- NormPair replacement.
- Period-4 clock replacement.

It considers three theorem relations:

- Watkins-target invariance.
- One-step/full-step equivariance.
- Iterated-step equivariance.

The sixth raw form is not emitted when it is already represented by the stronger full-step equivariance class. The current quotient therefore removes the iterate consequence and retains only minimal representatives.

The current basis candidates are:

- Watkins target is invariant under NormPair replacement.
- Watkins target is invariant under a four-phase clock shift.
- The canonical full step commutes with NormPair replacement.
- The canonical full step commutes with a four-phase clock shift.

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

The Mercury quotient therefore keeps a smaller basis rather than emitting every syntactic consequence. This is an e-graph-style use of equivalence classes: canonicalize symbolic theorem forms first, then send only minimal representatives to the proof checker.

This is deliberately domain-specific rather than a general optimizer. The semantic boundary remains the Agda learner. Mercury is only reducing redundant theorem search.

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
