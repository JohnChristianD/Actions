# Theorem composition improvements — 2026-09-26

## Scope

This pass closes the strongest proof-relevant composition seams identified in the canonical learner theorem graph. The source of proof authority remains `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`; Mermaid remains a projection.

## Closed improvements

### 1. Arbitrary-length token generation

Added `CanonicalTokenArbitraryLengthGenerationTheorem` and
`canonical-token-arbitrary-length-generation-theorem`.

The package consumes the existing:

- `canonicalTokenStep-conjugacy`
- `canonicalTokenListState-conjugacy`
- `canonicalToken-prefix-monoid-homomorphism`
- `canonicalTokenLogitTrace-append`

It exposes exact state conjugacy, prefix-monoid structure, and arbitrary finite-list logit-trace append composition in one proof-relevant record. This closes the previously documented gap where the constituent theorems existed but no single record packaged the full arbitrary-length generation surface.

The construction matches the standard algebraic picture: finite lists form the free monoid on a token set, and a set action extends to a free-monoid action whose concatenation law composes successive state transformations. urlnLab: actionhttps://ncatlab.org/nlab/show/action urlnLab: free monoidhttps://ncatlab.org/nlab/show/free%2Bmonoid

### 2. Orbit injectivity

The canonical learner already had `canonicalOrbit-state-injective` after the clock-removal work, so no duplicate theorem was added.

The generic frontier was strengthened instead with `NatSuccessorProgressWitness`, `successorMeasureAfterIterate`, and `successorMeasureOrbitInjective`. This factors the reusable mathematical kernel away from the canonical learner: an exact successor-valued measure gives injective orbit indices by cancellation.

The canonical `totalCount` witness remains the concrete instance. This is strictly stronger as an API boundary than repeating the learner-specific proof while preserving the existing theorem name and graph surface.

### 3. Iterated F4 / NormPair factor stability

Added `CanonicalF4NormPairIterateFactorStabilityTheorem` and
`canonical-f4-normPair-iterate-factor-stability-theorem`.

The package combines the already-closed F4/NormPair one-step factor theorem with:

- iterated `normPairWeightPlusOne` invariance,
- iterated persistent-GRU invariance,
- iterated NormPair quotient compatibility.

This makes the downstream iterate-stability interface explicit without claiming convergence, equilibrium, or an economic existence theorem.

## Boundary retained

No new Hodge-Maxwell inhabitant, equilibrium witness, market-clearing witness, supporting-price witness, or stationary-measure conclusion is manufactured by this pass. Those remain explicit conditional/frontier interfaces.

## Graph policy

The graph now exposes the three closed seams, while proof authority remains the Agda theorem monolith. A graph edge is not treated as proof evidence.

## Verification status

The branch was created from current `main` and all source mutations were made through the repository's GitHub API surface. Agda/Mercury execution still needs the repository CI gate; no local Agda toolchain was available in this execution environment.

## Provenance

Before: existing component theorems and graph candidates.

Change: package the arbitrary-length token generation closure, factor the reusable successor-measure orbit injection kernel, and package iterated F4/NormPair factor stability.

Why: remove duplicated proof topology, close real composition seams, and keep conditional cross-domain claims witness-gated.



## Search closure — 2026-09-26

A fresh repository search reconciles the remaining improvement queue against the current main proof surface.

### 4. Exact-growth spine

canonicalTotalCountAfter already proves the stronger iterate equation: totalCount(lcbCounts(iterateCanonical K n s)) ≡ totalCount(lcbCounts s) + n.

The generic frontier already derives NatSuccessorProgressWitness, successorMeasureAfterIterate, and successorMeasureOrbitInjective, while canonicalOrbit-state-injective exposes the canonical collision ⇒ equal-horizon theorem. No duplicate collision theorem is warranted. The graph is being sharpened so the exact-growth node is visibly upstream of strict progress and orbit injectivity.

The Agda standard library independently exposes natural-number addition cancellation (+-cancelˡ-≡), confirming that the cancellation kernel is ordinary Nat algebra rather than a bespoke clock argument.

### 5. Recurrent-prefix versus free-monoid action surfaces

The search found two distinct abstractions, not one obvious duplicate:

- RecurrentPrefixMonoidHomomorphism packages unit/append laws for recurrent prefix endomorphisms.
- FreeMonoidActionHomomorphism is consumed by the commuting-square transport theorem.

The current freeMonoidActionHomomorphism-from-square and canonicalCount-freeMonoidActionHomomorphism already provide a separate observation/action transport seam. Therefore Ponytail does not justify deleting either record yet. A future adapter should be added only if it proves an actual reusable conversion between the two semantics.

### 6. Expressivity / finite-state boundary

The repository now has the correct proof boundary for finite-state expressivity: the canonical orbit is injective in its horizon index, but a strict separation theorem still needs an explicit baseline class, inclusion, connected witness, and nonrepresentability proof. The search found no existing iterateCollision theorem because canonicalOrbit-state-injective already supplies that proposition.

This remains consistent with recurrent-expressivity literature: Svete & Cotterell (EMNLP 2023) study precise representational classes and finite-state comparisons, but those external results do not supply the repository-specific Agda witness or inclusion/nonrepresentability terms.

### 7. Hodge-Maxwell obstruction graph

The negative surfaces already exist as first-class graph nodes:

- hodgeMaxwell-globalEncode-noninjective-refutes-connected-representation
- hodgeMaxwell-discontinuous-gru-refutes-connected-representation

They consume the same carrier-polymorphic representation boundary and prevent unconditional promotion when the explicit collision/continuity premise fails. No new theorem is required for this improvement; the remaining work is graph readability.

### 8. Economics and convergence boundary

The current frontier already keeps learner factor stability, convergence, fixed-point closure, market clearing, supporting prices, and equilibrium existence separate. No theorem was found that justifies collapsing these interfaces. The search therefore confirms the existing conditional graph rather than adding a spurious learner→equilibrium implication.

### 9. Exact scan versus complexity

The repository contains LogarithmicPrefixScanComplexityTheorem, whose fields explicitly require both an exact scan law and separate operator/span/work certificates. This is the right seam: exact associative prefix composition does not itself discharge a machine-level complexity certificate. Blelloch's classical scan work supplies the external algorithmic precedent for logarithmic parallel depth, but the repository still needs its own operator representation and span witness before promoting a complexity result.

### Search disposition

The queue is now classified as:

- Already proved and exposed: exact iterate growth, generic strict progress, orbit-index injectivity, Hodge-Maxwell obstruction consumers, conditional economic frontier.
- Graph refinement only: exact-growth → strict-progress/orbit-injectivity visibility; exact scan versus complexity separation.
- Needs a genuine future semantic adapter: recurrent-prefix monoid surface ↔ free-monoid-action surface.
- Still frontier-gated: finite-state function-class separation and any unconditional learner→economic-equilibrium bridge.

External references checked 2026-09-26:
- Agda Data.Nat.Properties: +-cancelˡ-≡.
- Svete & Cotterell, Recurrent Neural Language Models as Probabilistic Finite-state Automata, EMNLP 2023.
- Blelloch, Prefix Sums and Their Applications, CMU-CS-90-190.
### 10. nLab homomorphism/action distinction

The supplied nLab definitions sharpen the reason the two repository abstractions should remain separate.

A monoid homomorphism preserves the monoid multiplication and identity. In the action viewpoint, a monoid action is a functor from the delooping `BM` into the target category, equivalently a map `M × X → X` satisfying unit and composition laws. An action homomorphism is correspondingly an equivariant map between actions. urlnLab: homomorphismhttps://ncatlab.org/nlab/show/homomorphism urlnLab: actionhttps://ncatlab.org/nlab/show/action

That distinction maps directly onto the repository search:

- `RecurrentPrefixMonoidHomomorphism` is the algebraic prefix-composition surface: it packages preservation of the prefix monoid structure by recurrent endomorphisms.
- `FreeMonoidActionHomomorphism` is the action/transport surface: it packages the commuting-square relationship between source feature transitions, target transitions, and observations.
- `freeMonoidActionHomomorphism-from-square` explicitly constructs the latter from a commuting-square witness, so it is not merely a second spelling of the former.
- `canonicalCount-freeMonoidActionHomomorphism` is a canonical learner instance of the action-transport surface.

Therefore the nLab distinction is evidence against the proposed Ponytail deletion: these are different semantic contracts even when both expose concatenation-compatible behavior. The minimal future improvement is an explicit adapter only if the codebase needs to transport a proved monoid-homomorphism package into an equivariant action-homomorphism package (or conversely). Until such a use exists, adding an adapter would be speculative abstraction.

This also explains why the arbitrary-length token theorem can legitimately consume `canonicalToken-prefix-monoid-homomorphism` while the commuting-square machinery separately consumes `FreeMonoidActionHomomorphism`: the former is preservation of an algebraic composition law; the latter is compatibility of actions across a square.

External primary source checked 2026-09-26: nLab homomorphism and action definitions.