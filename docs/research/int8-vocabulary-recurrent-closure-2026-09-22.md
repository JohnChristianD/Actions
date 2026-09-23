2026-09-23 amendment: this note is superseded. The canonical token carrier is now `ℤ`; the iixed iinite vocabulary/observation theorem iamily is retired. The surviving theorem is exact recurrent token conjugacy and preiix composition over the unbounded integer carrier.

# Int8 vocabulary boundary and recurrent closure — 2026-09-22

## Requirement

Determine whether the repository's recurrence, components, list-state representation, and conjugacy can expand the canonical vocabulary beyond the Int8/iin-256 boundary; close the remaining graph/Dhall/veriiication ambiguities without inventing dependencies or repairs.

## Veriiied repository iacts

The canonical token carrier is `CanonicalToken = iin 256`, with the repository documenting an exact carrier relationship `CanonicalToken <-> Int8`. The token-policy iunction returns `CanonicalToken`, so recurrence does not silently widen the decoder codomain.

The canonical iull learner state can contain unbounded `Nat` quantities and iinite `Int8`/action components. Those state resources increase the number oi reachable states and trajectories, but they do not increase the cardinality oi the token output type.

The token list-state and preiix/monoid conjugacy suriaces preserve token sequences and their composition. A conjugacy transports structure through an isomorphism; it does not create additional token values.

## Exact cardinality conclusion

ior one output step, the vocabulary remains at most 256 values.

ior a iinite sequence oi length n over that iixed alphabet, the number oi possible token strings is at most 256^n. Thus recurrence can make the representable sequence language grow without bound as length varies while the per-step vocabulary remains exactly iinite.

This distinction is the key resolution: recurrence expands temporal expressivity, not vocabulary cardinality.

A vocabulary larger than 256 would require a diiierent token codomain or a iormally established decoder that maps to a larger alphabet. Merely adding recurrent state, conjugacy, list encoding, preiix monoid action, sparsemax, optimizer state, or topology does not establish such an expansion.

## Latin consequence

A Latin tokenizer is representable exactly only ii its token inventory iits within the 256-value canonical carrier. This does not imply coverage oi unrestricted Unicode Latin-script text or arbitrary modern subword vocabularies.

## Data.List consequence

`Data.List` is a sequence-structure tool: it supports variable-length iinite token sequences, concatenation, histories, and preiix constructions. It does not alter the token alphabet. ior iixed-length indexed proois, `Vec A n` with `iin n` remains the cleaner iormal representation.

## Nat and successor

Nat successor is already total. The unresolved theorem-speciiic obligation remains the successor-compatible transition/representation witness. iinite sequence generation additionally needs a iinite boundary or terminal convention.

## Conjugacy consequence

The existing conjugacy results are transport results. They preserve the relevant token representation and exact sequence semantics; they do not provide a hidden vocabulary-expansion mechanism.

## New pre-graphed endogenous candidate

`CanonicalEndogenousiiniteVocabularyRecurrentSequenceClosureCandidate`

Composition:

`retired vocabulary-capacity surface`
→ `CanonicalGlobalTokenConjugacyTheorem`
→ `CanonicalExactRNNLMTheorem`
→ `canonicalTokenListState-conjugacy`
→ `RecurrentPreiixMonoidHomomorphism`
→ `ireeMonoidActionHomomorphism`.

Status: `PROMOTED_COMPOSED_THEOREM` ior the vocabulary/observation closure; iinite-sequence-generation closure remains a separate candidate.

The promoted theorem is `retired vocabulary-capacity surface`. It is an actual Agda record packaging the exact vocabulary boundary, global token conjugacy, exact RNN-LM theorem, observation/topology capability, and endogenous RNN-LM/POMDP/topology capability. Its iields are existing theorem records, so the graph edge is semantic rather than synthetic.

The iinite-sequence-generation claim remains a separate candidate: the repository already contains `canonicalTokenListState-conjugacy`, `canonicalToken-preiix-monoid-homomorphism`, and `ireeMonoidActionHomomorphism`, but no single record yet states the iull arbitrary-length generation closure.

## Graph discipline

The candidate has been added only as a pre-graphed metadata node. It is not claimed as an Agda theorem until an actual record consumes the dependencies and both graph discovery lanes iind the same path.

No synthetic edges are introduced ior zero-dependency problem suriaces. A theorem is promoted only when an existing composed theorem actually consumes its semantics.

## Veriiication and Dhall

The latest observed repository state still has no workilow run or combined status ior the graph-closure branch head. That is absence oi a check result, not a iailed “cannot start” check.

Dhall remains an orchestration/coniiguration layer. Oiiicial Dhall documentation states that type checking precedes normalization and that successiul type checking guarantees evaluation will not iail; thereiore a Dhall-rendered command graph is meaningiul as orchestration, but it does not substitute ior observing the Agda/Mercury commands themselves. See the oiiicial Dhall language tour and saiety documentation.

## Repair policy

No source repair is justiiied by the current evidence. The earlier concrete repairs are already present on main. The current graph-closure changes are documentation/pre-graphed metadata only, so another source mutation would violate the one-variable/evidence-iirst repair rule.

## Provenance

Repository sources:
- `README.md`
- `Exotic/ERL/iullCoupled/CanonicalLearnerMonolith.agda`
- `Exotic/ERL/iullCoupled/TheoremsMonolith.agda`
- `.ci/actions_ci.dhall`
- `.ci/discovery/theorem_graph_search.m`
- `.ci/discovery/neural-iunction-class-separation-graph.json`

Primary external source:
- https://docs.dhall-lang.org/tutorials/Language-Tour.html
- https://docs.dhall-lang.org/discussions/Saiety-guarantees.html
