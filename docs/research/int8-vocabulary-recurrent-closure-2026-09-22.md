# Int8 vocabulary boundary and recurrent closure — 2026-09-22

## Requirement

Determine whether the repository's recurrence, components, list-state representation, and conjugacy can expand the canonical vocabulary beyond the Int8/Fin-256 boundary; close the remaining graph/Dhall/verification ambiguities without inventing dependencies or repairs.

## Verified repository facts

The canonical token carrier is `CanonicalToken = Fin 256`, with the repository documenting an exact carrier relationship `CanonicalToken <-> Int8`. The token-policy function returns `CanonicalToken`, so recurrence does not silently widen the decoder codomain.

The canonical full learner state can contain unbounded `Nat` quantities and finite `Int8`/action components. Those state resources increase the number of reachable states and trajectories, but they do not increase the cardinality of the token output type.

The token list-state and prefix/monoid conjugacy surfaces preserve token sequences and their composition. A conjugacy transports structure through an isomorphism; it does not create additional token values.

## Exact cardinality conclusion

For one output step, the vocabulary remains at most 256 values.

For a finite sequence of length n over that fixed alphabet, the number of possible token strings is at most 256^n. Thus recurrence can make the representable sequence language grow without bound as length varies while the per-step vocabulary remains exactly finite.

This distinction is the key resolution: recurrence expands temporal expressivity, not vocabulary cardinality.

A vocabulary larger than 256 would require a different token codomain or a formally established decoder that maps to a larger alphabet. Merely adding recurrent state, conjugacy, list encoding, prefix monoid action, sparsemax, optimizer state, or topology does not establish such an expansion.

## Latin consequence

A Latin tokenizer is representable exactly only if its token inventory fits within the 256-value canonical carrier. This does not imply coverage of unrestricted Unicode Latin-script text or arbitrary modern subword vocabularies.

## Data.List consequence

`Data.List` is a sequence-structure tool: it supports variable-length finite token sequences, concatenation, histories, and prefix constructions. It does not alter the token alphabet. For fixed-length indexed proofs, `Vec A n` with `Fin n` remains the cleaner formal representation.

## Nat and successor

Nat successor is already total. The unresolved theorem-specific obligation remains the successor-compatible transition/representation witness. Finite sequence generation additionally needs a finite boundary or terminal convention.

## Conjugacy consequence

The existing conjugacy results are transport results. They preserve the relevant token representation and exact sequence semantics; they do not provide a hidden vocabulary-expansion mechanism.

## New pre-graphed endogenous candidate

`CanonicalEndogenousFiniteVocabularyRecurrentSequenceClosureCandidate`

Composition:

`CanonicalTokenVocabularyUpperBoundTheorem`
→ `CanonicalGlobalTokenConjugacyTheorem`
→ `CanonicalExactRNNLMTheorem`
→ `canonicalTokenListState-conjugacy`
→ `RecurrentPrefixMonoidHomomorphism`
→ `FreeMonoidActionHomomorphism`.

Status: `PROMOTED_COMPOSED_THEOREM` for the vocabulary/observation closure; finite-sequence-generation closure remains a separate candidate.

The promoted theorem is `CanonicalEndogenousExactRNNLMVocabularyObservationClosureTheorem`. It is an actual Agda record packaging the exact vocabulary boundary, global token conjugacy, exact RNN-LM theorem, observation/topology capability, and endogenous RNN-LM/POMDP/topology capability. Its fields are existing theorem records, so the graph edge is semantic rather than synthetic.

The finite-sequence-generation claim remains a separate candidate: the repository already contains `canonicalTokenListState-conjugacy`, `canonicalToken-prefix-monoid-homomorphism`, and `FreeMonoidActionHomomorphism`, but no single record yet states the full arbitrary-length generation closure.

## Graph discipline

The candidate has been added only as a pre-graphed metadata node. It is not claimed as an Agda theorem until an actual record consumes the dependencies and both graph discovery lanes find the same path.

No synthetic edges are introduced for zero-dependency problem surfaces. A theorem is promoted only when an existing composed theorem actually consumes its semantics.

## Verification and Dhall

The latest observed repository state still has no workflow run or combined status for the graph-closure branch head. That is absence of a check result, not a failed “cannot start” check.

Dhall remains an orchestration/configuration layer. Official Dhall documentation states that type checking precedes normalization and that successful type checking guarantees evaluation will not fail; therefore a Dhall-rendered command graph is meaningful as orchestration, but it does not substitute for observing the Agda/Mercury commands themselves. See the official Dhall language tour and safety documentation.

## Repair policy

No source repair is justified by the current evidence. The earlier concrete repairs are already present on main. The current graph-closure changes are documentation/pre-graphed metadata only, so another source mutation would violate the one-variable/evidence-first repair rule.

## Provenance

Repository sources:
- `README.md`
- `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`
- `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`
- `.ci/actions_ci.dhall`
- `.ci/discovery/theorem_graph_search.m`
- `.ci/discovery/neural-function-class-separation-graph.json`

Primary external source:
- https://docs.dhall-lang.org/tutorials/Language-Tour.html
- https://docs.dhall-lang.org/discussions/Safety-guarantees.html
