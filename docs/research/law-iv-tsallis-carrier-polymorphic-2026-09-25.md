# Law IV carrier-polymorphic Tsallis audit — 2026-09-25

## Decision

Law IV can be generalized at the representation-theorem layer without importing Real, Rational, Vec, or Fin n. The implementation uses an arithmetic-free interface:

- CarrierPolymorphicStatisticalRepresentation
- TsallisCompatibleStatisticalRepresentation

## What changed

Exotic/ERL/FullCoupled/TsallisStatisticalRepresentation.agda now provides the carrier-polymorphic proof kernel.

Exotic/ERL/FullCoupled/GRUStatisticalInjectivity.agda instantiates that kernel for the existing canonical GRU observation and exposes canonicalGRUTsallisCompatibleRepresentation, canonicalGRUTsallisCompatibleInjective, and canonicalGRUTsallisCompatibleDistinguishability.

The existing CanonicalGRUStatisticalInjectivityTheorem remains intact for compatibility.

## What is deliberately not claimed

The generic module does not formalize the numerical Tsallis entropy/q-log construction. The official Tsallis material motivates the statistical interpretation, but it does not supply an Agda proof of the repository's representation inverse. Therefore the new module treats Tsallis-compatible as a structural interface, not as an imported external axiom.

The current canonical learner still contains FiniteRational and SignedQLogControl in its concrete full state. This change does not rewrite that executable learner state. It removes those concrete arithmetic choices from the abstract Law-IV injectivity surface.

Likewise, the generic observation carrier does not require Vec or Fin n. Any future concrete Tsallis observation carrier can be supplied independently.

## Closure consequence

```text
concrete GRU observation
        |
        v
CarrierPolymorphicStatisticalRepresentation
        |
        +--> decode ∘ encode = id
        |
        v
generic injectivity
        |
        v
Tsallis-compatible Law IV surface
```

It does not close the four-law physics frontier. Law-I/Law-III inverse witnesses and the physics-to-learner transition witness remain separate proof obligations.

## Verification boundary

The repository connector was used to inspect the canonical Agda monoliths before editing and to trace consumers of the Law-IV theorem. No theorem was inferred solely from the external Tsallis source. Agda/CI execution is not claimed here unless a workflow result is observed for the new commit.
