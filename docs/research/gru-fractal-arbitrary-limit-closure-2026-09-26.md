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
- `.ci/discovery/gru-fractal-arbitrary-limit-closure-2026-09-26.mmd`: end-to-end composition/search projection.
- `EGraphSemanticTransport.agda`: proof-only e-graph/A* transport kernel.
- `RepositorySemanticEGraphClosure.agda`: repository-wide semantic-family closure.

The new module is `--safe`. No unconditional convergence or limit-existence theorem is introduced.
