# Constructive Inversion + Exact Search

Date: 2026-10-05

## Verified sources

- agda2hs documentation: `agda2hs-base` is the bundled Agda library for the Haskell extraction tool; the documentation states that agda2hs compiles an Agda module and its dependencies to Haskell and that normal Agda standard-library use is unsupported in agda2hs projects. https://agda.github.io/agda2hs/introduction.html
- Todd Waugh Ambridge, *Exact Real Search: Formalised Optimisation and Regression in Constructive Univalent Mathematics* (2024): the framework combines searchable types, closeness spaces, explicit uniform-continuity information, and constructive search/optimisation. https://arxiv.org/abs/2401.09270
- Teegen, Prott, Bunkenburg, *Haskell^-1: Automatic Function Inversion in Haskell* (Haskell '21): automatic inversion is based on a functional-logic extension with nondeterminism and free variables; functional patterns are expressed through inverse calls, with a single-solution/compatible-solutions requirement for deterministic Haskell semantics. https://finnteegen.de/publications/Haskell-1AutomaticFunctionInversionInHaskell.pdf
- TypeTopology TWA source: `TWA.Thesis.Chapter3.SearchableTypes` defines `searchable`, `csearchable`, and the construction of searchability via explicitly uniformly-continuous decidable predicates; `ClosenessSpaces` defines `f-ucontinuous` and `p-ucontinuous` using explicit natural-number moduli.
- Existing repository pipeline: TypeTopology, agda2hs-base, and the inversion plugin are already pinned in `flake.nix`.

## Architectural decision

The Agda theorem layer now contains a generic `ExactSearchInversion.ExactSearchEquivalence` contract. It carries a forward map, inverse, left/right inverse proofs, forward/inverse uniform-continuity witnesses, and c-searchability of the source space.

The theorem `inverse-preserves-csearchability` transports TWA c-searchability from the source space to the target by pulling back each decidable uniformly-continuous predicate along the forward map and using the inverse as the preimage witness.

The theorem `inverse-selects-preimage` gives the proof-theoretic counterpart of automatic inverse computation: whenever the forward map sends `x` to `y`, the certified inverse returns that same `x`.

This does not claim that an arbitrary non-injective function has a canonical inverse. The inversion contract is deliberately stronger: it records an equivalence/single-solution regime, matching the deterministic boundary described in the Haskell inversion work.

## Mercury role

Mercury now has a separate capability-space A* discovery pass. It searches semantic declarations for three independent capabilities:

1. inversion/injectivity/equivalence,
2. exact search/searchability,
3. uniform continuity/closeness.

The pass produces candidate compositions rather than pretending those candidates are Agda proofs. Agda remains the proof authority. E-graph saturation is retained for quotienting and validation, not as the definition of theorem novelty.

