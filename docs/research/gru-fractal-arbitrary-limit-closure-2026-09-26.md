# Arbitrary-limit GRU fractal closure and e-graph/A* composition — 2026-09-26

## Core correction

The canonical Integer/GRU representation already has the important global mechanism: when an encoder has a global decoder with a left-inverse law, global injectivity is derived. A separate global “separation” axiom is unnecessary for that encoder.

The new limit boundary is different. For a new limit encoder `limitEncode`, injectivity is immediate once a decoder survives the limit with

`limitDecode (limitEncode s) ≡ s`.

Therefore the repository now derives limit separation from a typed `LimitLeftInverse` record instead of treating separation as an unrelated mathematical principle. The distinction is:

`global left inverse → global injectivity`

and, for the limit representation,

`limit-surviving left inverse → limit separation → limit injectivity`.

The approximation/limit record remains intentionally conservative: convergence or completeness alone does not prove separation.

## E-graph + A* closure

The repository already contains the proof-only e-graph kernel in `EGraphSemanticTransport.agda` and the repository-wide indexed closure in `RepositorySemanticEGraphClosure.agda`. The discovery side uses Mercury's `semantic_law` graph and A*-style cost-guided traversal; Agda `--safe` remains the proof authority.

The completed composition path for this boundary is:

`GRU decode-after-encode`
→ `global GRU injectivity`
→ `level-indexed injectivity`
→ `injective inter-level transport`
→ `finite/indexed fractal composition`
→ `compatible approximation`
→ `limit representation`
→ `limit-surviving left inverse`
→ `derived limit separation`
→ `arbitrary-limit injectivity`.

A* may choose a low-cost discovery path, but its cost or heuristic is never semantic evidence. A typed e-graph path is sound only through the existing Agda semantic interpretation.

## Physics four-law interpretation

The September 2026 Navier–Stokes formalization is useful here as a continuation boundary. It does not prove the four physics MARL laws and it is not an inhabitant of the GRU fractal kernel. Its relevant role is to block the invalid inference

`finite/local dynamical structure → arbitrary global smooth continuation`.

For the four-law interpretation, the positive route remains explicit:

`Law-I witness + Law-III witness + physics→learner transition`
→ `finite-step conjugate dynamics`
→ `fractal composition`.

The Navier–Stokes result is a negative/guard edge around arbitrary continuation, not a positive proof edge into the four laws.

## Economic boundary

The same graph discipline is retained downstream. Exact representation/injectivity does not manufacture convergence, fixed points, market clearing, supporting prices, or Walrasian equilibrium existence. Economic adapters require their own representation and witness contracts.

## Formal files

- `GRUFractalLimitClosure.agda`: explicit approximation/limit-separation contract.
- `GRUFractalEGraphAStarLimitComposition.agda`: derives limit separation/injectivity from a surviving left inverse and reuses the proof-only e-graph path soundness kernel.
- `GRUFractalLimitDecoderSurvival.agda`: derives the limit left-inverse law from coherent finite decoder projections; it does not assert limit existence or decoder coherence without witnesses.
- `.ci/discovery/gru-fractal-arbitrary-limit-closure-2026-09-26.mmd`: end-to-end composition/search projection.
- `EGraphSemanticTransport.agda`: proof-only e-graph/A* transport kernel.
- `RepositorySemanticEGraphClosure.agda`: repository-wide semantic-family closure.

The new module is `--safe`. No unconditional convergence or limit-existence theorem is introduced.
## Concrete canonical Integer-GRU seam

The previously abstract “global left inverse” node is now instantiated on the repository's actual unbounded integer token surface. CanonicalToken = ℤ, while Int8 is an exact ℤ wrapper, so canonicalTokenDecode = code gives the total identity law

canonicalTokenDecode (canonicalTokenEncode t) ≡ t.

From that law, Agda derives global token-encoding injectivity. The same composition packages the existing CanonicalGlobalTokenEncodingConjugacyTheorem, so the concrete chain is now:

Integer token left inverse → token-encoding injectivity → discrete-topology continuity → exact recurrent conjugacy.

This is stronger than treating limitSeparation as a primitive assumption for the existing global representation. It still does not instantiate a genuine analytic fractal-limit carrier: a future limit representation must supply its own limit decoder/projection/coherence or another surviving left-inverse construction. The discrete continuity theorem is deliberately not a claim of analytic continuity.

The e-graph/A* interpretation therefore has a concrete source node for the global-left-inverse edge. A* may discover the path, but Agda remains the authority for every equality.


## A* target closure update

The canonical theorem monolith now exposes a generic composition target named
`CanonicalIntegerGRUFractalLimitCompositionTheorem`. Its inputs are explicit:
a genuine limit-encoding kernel must be supplied. The theorem combines the already
proved global Integer-GRU conjugacy with the supplied surviving limit left inverse
and derives limit injectivity via `gruFractalLimitComposition-limitInjective`.

This deliberately closes the **search/composition seam**, not the analytic-limit
frontier. No concrete `limitEncode`, convergence theorem, projection family, or
limit decoder is manufactured by this target. The Mercury discovery graph now
registers the target for A*-style traversal; Agda remains authoritative.

The resulting status is therefore:
`global Integer-GRU left inverse/conjugacy` = proved;
`generic limit-left-inverse ⇒ limit-injectivity composition` = proved;
`concrete fractal limit carrier + surviving decoder` = explicit frontier.
