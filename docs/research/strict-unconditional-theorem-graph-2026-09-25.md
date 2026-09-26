# Strict unconditional theorem graph for the full monolith

This graph deliberately uses a stronger admission rule than the ordinary theorem/e-graph inventory.

A node is promoted only when the monolith contains a closed proof term for it and the theorem does not require an external condition, certificate, data, convergence, equilibrium, topology, or existence record as an input. Universal mathematical variables and hypotheses internal to a proved implication are allowed.

The graph therefore contains proved algebraic laws, exact compositions, exact impossibilities, concrete countermodels, and closed economic embeddings. It does not promote conditional existence interfaces merely because their records are well-typed.

## Stability and F4

The unconditional chain now includes:

`canonical-f4-global-optimizer-stability-theorem`
→ `canonical-f4-normPair-sure-stability-composition-theorem`
→ `canonical-normPair-quotient-factor-transition-theorem`
→ `canonical-f4-normPair-factor-stability-theorem`.

This is the unconditional stability/factorization result.

It does **not** contain an unconditional exact-`thetaQ` infinite-horizon bound. The closed theorem `f4-unit-forcing-linear-growth` instead proves a forcing ray with linear growth, and `f4-unit-forcing-no-upper-bound` derives the corresponding obstruction once the specified zero initial state is supplied.

## Economic boundary

The strict graph includes the closed impossibility:

`noUnconditionalMegaGeneralizedWalrasianExistence`

and the stronger F4/NormPair/economic-injectivity impossibility:

`noUnconditionalMegaWalrasianExistenceEvenWithF4NormPairEconomicInjectivity`.

Thus no conditional equilibrium record is being silently promoted to an unconditional existence theorem.

## Recursive Radner

`recursiveRadner-generalized` is included as an unconditional construction of Recursive Radner as an instance of the repository's singular `MegaGeneralizedWalrasianEquilibrium` ontology.

The existence transport `recursiveRadner-existence-embeds` is intentionally excluded from the strict theorem graph because it consumes a supplied `RecursiveRadnerExistence` witness. The graph therefore distinguishes:

Radner semantics / embedding
from
Radner existence.

## Stationarity

The strict graph keeps the proved full-state obstruction, now expressed through the exact successor total-count / no-fixed-point family. It does not claim an unconditional invariant-probability measure theorem. A stationary distribution requires an explicit probability space and invariant-measure semantics; those are not fabricated from deterministic factor stability.

## Inventory

Machine-readable inventory: `.ci/discovery/strict-unconditional-theorems-monolith.json`.

Mermaid graph: `.ci/discovery/strict-unconditional-theorems-monolith.mmd`.

At this snapshot, the strict graph contains 77 theorem/impossibility nodes and 229 source-derived proof-term edges. Another 85 theorem-like declarations are excluded because they require external proof/data records or are not theorem/impossibility declarations under the strict rule.

## Finite-candidate price classification boundary

The new `finiteCandidatePriceSearch` kernel is intentionally absent from the strict unconditional theorem graph. Although its recursion is total, its theorem interface consumes an explicit `FiniteCandidateDecision` procedure. Under the strict graph admission rule, that makes it a supplied-certificate/classification interface rather than a closed unconditional economic theorem.

The kernel is therefore tracked in the broader economic frontier as a constructive finite/discrete candidate-classification result. It does not alter the closed impossibility `noUnconditionalMegaGeneralizedWalrasianExistence`.
