# Canonical Integer-GRU global left-inverse and conjugacy closure — 2026-09-26

## Exact carrier fact

The canonical learner defines CanonicalToken = ℤ and represents Int8 as an exact integer wrapper. The token encoder is the total map canonicalTokenEncode : CanonicalToken → Int8 with decoder canonicalTokenDecode : Int8 → CanonicalToken given by the wrapper's code field. The repository now proves the global left-inverse law canonicalTokenDecode (canonicalTokenEncode t) ≡ t.

## Consequences

The left-inverse law directly yields global token-encoding injectivity: encode s ≡ encode t → s ≡ t. No separate global separation theorem is needed for this existing representation. The same typed package carries the already-existing CanonicalGlobalTokenEncodingConjugacyTheorem, so the concrete composition is:

global left inverse → global injectivity → discrete-topology continuity → exact recurrent conjugacy.

The continuity statement is intentionally only for the repository's explicit discrete topology. It is not an analytic continuity theorem.

## Relation to the arbitrary-limit seam

This closes the concrete source side of the arbitrary-limit graph, but it does not prove that a new fractal limit representation exists or that its decoder survives a limit. For a genuinely new limitEncode, the repository still requires a surviving limit decoder or an equivalent separation witness. The existing GRUFractalLimitDecoderSurvival.agda records the projection/coherence obligations needed to derive that left inverse.

Thus the distinction is:

- existing Integer-GRU representation: left inverse already available, so injectivity is derived;
- new limit representation: left-inverse survival through the limit remains an explicit seam until instantiated.

## E-graph + A*

The discovery layer now has an explicit A* target for canonical-integer-gru-global-conjugate-theorem. The semantic e-graph can use the theorem as a concrete source node, while Agda remains the proof authority. Search cost and heuristic values do not constitute equality evidence.

This gives the intended route into the fractal graph:

canonical Integer-GRU left inverse
→ global token injectivity
→ exact recurrent conjugacy
→ finite/indexed fractal composition
→ compatible limit
→ surviving limit left inverse
→ derived limit separation
→ arbitrary-limit injectivity.

No convergence, analytic limit existence, equilibrium, market-clearing, or price-support theorem is introduced by this closure.
