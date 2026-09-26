# GRU fractal domain adapters — 2026-09-26

The generic FractalInjectiveComposition kernel now has explicit domain-facing contracts for Physics and Economics.

## Physics

PhysicsGRUFractalAdapter consumes the existing FourLawOneStepWitnessContract together with a FractalInjectiveComposition. This makes the intended composition precise:

four-law semantic witness
+ level-indexed GRU representation
+ explicit refinement/transport injectivity
+ transport compatibility
→ GRU-injective physics fractal representation.

The adapter deliberately does not provide Law-I or Law-III inhabitants. The repository's current frontier explicitly marks those concrete witnesses as missing. Therefore this module does not convert the conditional four-law closure into an unconditional theorem.

## Economics

EconomicsGRUFractalAdapter requires learner↔economic inverse laws and one-step conjugacy, plus a genuine FractalInjectiveComposition over the economic representation.

The economic seam is now stricter: a level index alone is not accepted as a fractal law. The adapter requires an explicit economicLevelTransport, an injectivity proof for that transport, an economic observation map, and a representation-compatibility equation connecting economic inter-level transport to the kernel's observation transport.

The intended chain is:

economic level relation
→ economic inter-level transport
→ transport injectivity
→ representation compatibility
→ fractal GRU-injective economic representation.

This prevents a nominal Nat index or identity placeholder from being mistaken for a substantive cross-scale economic theorem.

## Boundary

The formal implication remains:

local GRU injectivity + explicit scale transport + representation compatibility → fractal GRU injectivity.

It does not imply convergence, fixed points, market clearing, supporting prices, Walrasian existence, or commons preservation. Those remain independently witnessed or refuted on their existing theorem surfaces.

## Why no concrete Physics/Economics inhabitants are fabricated

The Physics side still lacks the concrete Law-I and Law-III semantic witnesses required by the repository's own contract. The Economics side has learner/economic transport infrastructure, but a nontrivial economic level/refinement law and compatible inter-level transport have not yet been established.

The adapter module therefore records the exact missing inputs rather than weakening the proof boundary with an identity placeholder and calling that a domain theorem.

## Primary repository surfaces

- Exotic/ERL/FullCoupled/GRUFractalInjectiveComposition.agda
- Exotic/ERL/FullCoupled/GRUFractalInjectiveCompositionCanonical.agda
- Exotic/ERL/FullCoupled/FourLawClosureWitnesses.agda
- Exotic/ERL/FullCoupled/GRUFractalDomainAdapters.agda