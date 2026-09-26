# GRU-injective fractal composition — 2026-09-26

## Summary

The repository now has a proof-relevant seam for distinguishing ordinary GRU injectivity from an indexed/self-similar composition claim.

The canonical Law-IV surface already proves GRU statistical injectivity by a decode-after-encode left inverse. The new kernel does not assume that every fractal representation is injective. Instead, it requires three explicit ingredients:

1. a level-indexed encode/decode pair with a left inverse at every level;
2. an explicit refinement relation between levels;
3. an injective inter-level transport that is compatible with the level-indexed encoding.

From these inputs, injectivity of the transported lower-level representation follows. This is the precise composition law needed before calling a scale-indexed representation fractal and GRU-injective.

## Repository evidence

`Exotic/ERL/FullCoupled/GRUStatisticalInjectivity.agda` contains the canonical GRU observation, decode, decode-after-encode equality, and injectivity theorem. Its mechanism is exact: applying the projection/decode map to an equality of encoded observations recovers equality of GRU states.

`Exotic/ERL/FullCoupled/GRUFractalInjectiveComposition.agda` introduces `FractalInjectiveComposition`. The module deliberately requires an explicit `Refines` relation. Merely having `Level → ...` families is therefore not called fractal. The kernel proves:

- `fractalLevelInjective`: every level representation is injective from its left inverse;
- `fractalTransportedEncodeInjective`: an injective refinement transport preserves injectivity of the transported representation.

`Exotic/ERL/FullCoupled/GRUFractalInjectiveCompositionCanonical.agda` instantiates the kernel with the canonical GRU observation, `Nat` as the level carrier, `≤` as the refinement relation, and identity inter-level transport. The instance is scale-invariant by construction, so it proves a concrete self-similar GRU representation without claiming that arbitrary fractals are GRU-injective.

## Logical boundary

The valid implication is:

GRU decode-after-encode
→ local GRU injectivity
→ level-indexed GRU injectivity
+ explicit injective scale transport
+ transport/encoding compatibility
→ transported fractal injectivity.

The invalid shortcut is:

self-similarity/fractal indexing
→ GRU injectivity.

The latter is not a theorem.

Likewise, fractalizing the Economics or Physics theorem graphs does not automatically import GRU injectivity. A domain theorem is GRU-injective only when its representation is connected to the GRU representation by an explicit injective adapter, inverse, or conjugacy/transport witness.

## Terminology

The repository should distinguish:

- **indexed**: a family parameterized by levels;
- **nested/self-similar**: the same law is repeated across related levels;
- **scale transport**: an explicit map carrying representations between levels;
- **fractal**: nested/self-similar structure together with an explicit level/refinement and composition/transport law.

This avoids promoting every level-indexed theorem to a fractal theorem.

## Scope

The current canonical instance uses identity transport. It therefore establishes the formal seam and a concrete scale-invariant GRU instance, but it does not yet establish a nontrivial learned or physical scale transformation. Such a transformation would require its own injectivity and compatibility witnesses.

The Economics and Commons nested theorems remain independent. In particular, the existing Commons nested counterexample still demonstrates that adding levels does not manufacture a missing aggregate conservation invariant.

## Verification

The new Agda modules are added explicitly to the Agda theorem/safe verification lanes in `.ci/actions_ci.dhall`. This is intentional: unlike the earlier `CommonsComposition.agda` situation, the new modules are not merely present on disk; CI is required to typecheck them.

Primary source:
- `Exotic/ERL/FullCoupled/GRUStatisticalInjectivity.agda`
- `Exotic/ERL/FullCoupled/GRUFractalInjectiveComposition.agda`
- `Exotic/ERL/FullCoupled/GRUFractalInjectiveCompositionCanonical.agda`