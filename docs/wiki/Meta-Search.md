# Meta-Search Architecture

Last audited: 2026-09-19 against `main` after the automated e-graph correction.

## Semantic authority

The learner's semantic universe is defined by the Agda source, not by Mercury.

The active semantic sources are:

- `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`
- `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

Both use `{-# OPTIONS --safe #-}`.

The Mercury layer consumes a mechanically extracted representation of those declarations. It does not define a separate hard-coded learner symbol registry.

## Roles

| Layer | Actual role |
|---|---|
| Agda learner monolith | Executable canonical learner semantics |
| Agda theorem monolith | Canonical theorem/proof surface |
| `learner_semantic_extractor.m` | Parses theorem-like declarations and derives source-level dependencies |
| `learner_semantic_manifest.m` | Reads the generated typed manifest |
| `novel_learner_theorem_discovery.m` | Selects extracted composite laws and generates Agda aliases |
| `symbolic_egraph.m` | Generic expression/e-class data structure and congruence rebuild |
| `interpolated_theorem_egraph.m` | Encodes manifest-derived law/dependency expressions for regression |
| Guix/Guile | Reproducible build, orchestration, and lane selection |
| Agda `--safe` | Acceptance authority for generated propositions |

## Current semantic pipeline

The current pipeline is:

```
CanonicalLearnerMonolith.agda
              +
TheoremsMonolith.agda
              |
              v
learner_semantic_extractor.m
              |
              v
learner-semantic-laws.tsv
              |
              v
learner_semantic_manifest.m
              |
              +-------------------------+
              |                         |
              v                         v
interpolated_theorem_egraph.m
              |
              +--> proof-compose associativity quotient
              |
              v
novel_learner_theorem_discovery.m
              |
              v
GeneratedNovelLearnerTheorems.agda
              |
              v
agda --safe
```

The dependency relation is obtained from occurrences of declarations already present in the source files. Composite status is derived from having at least two extracted dependencies and not being a reflexive declaration.

## No hard-coded learner symbol registry

There is deliberately no Mercury-side list defining the learner's semantic atoms, transformations, or observables.

In particular, the current `novel_learner_theorem_discovery.m` contains no equivalent of:

- a manually declared NormPair transformation grammar;
- a manually declared period-4 transformation grammar;
- a manually declared observable registry;
- a hand-written theorem candidate table.

Those descriptions belonged to an earlier discovery architecture and are no longer accurate.

The generated discovery report itself records:

```
"search_semantics": "learner-monolith semantic dependency extraction"
"symbolic_registry": false
"refl_as_composition": false
"proof_authority": "Agda --safe"
```

The semantics of the search are therefore endogenous in the limited, precise sense implemented by the repository: the candidate/source names and dependency graph come from the learner/theorem source itself.

## What the current "novel" executable actually does

The filename `novel_learner_theorem_discovery.m` is retained for CI continuity, but its present algorithm is not theorem synthesis over an independently authored grammar.

It:

1. extracts declarations from the canonical learner and theorem source;
2. reads the shared semantic manifest;
3. filters declarations marked composite;
4. emits named Agda aliases for those declarations;
5. writes a report describing the extraction.

The current generated module contains four source-owned theorem projections:

- `generatedSemanticDerived0 = T.canonicalStep-not-fixed`
- `generatedSemanticDerived1 = T.clockAfter`
- `generatedSemanticDerived2 = T.canonicalAperiodic`
- `generatedSemanticDerived3 = T.canonicalNoCountedTwoCycle`

It also records the manifest-derived e-graph associativity quotient count. These declarations are not automatically promoted into `TheoremsMonolith.agda`.

## Generic symbolic e-graph boundary

`.ci/discovery/symbolic_egraph.m` is a generic ground e-graph implementation.

Its expressions have the form:

```
atom(Symbol)
app(Symbol, Children)
```

Its e-graph uses:

- hash-consed enodes;
- finite e-class IDs;
- parent representatives;
- congruence rebuild;
- equivalence checks.

The symbols in this generic engine are merely strings carried by the expression representation. Semantic meaning comes from the manifest-derived construction that creates those expressions.

`interpolated_theorem_egraph.m` maps each extracted law into `semantic-law(...)` and each composite dependency list into `proof-compose(...)`. For dependency lists of length at least three, it constructs both left- and right-associated proof plans and merges their e-classes. Thus the e-graph performs an actual quotient over a source-derived algebraic identity, rather than merely storing nodes.

That quotient is symbolic normalization. It does not establish theorem truth; `agda --safe` does that. The regression requires a nonempty manifest graph and a nonzero associativity quotient.

## Trust boundary

The repository's trust order is:

```
Agda learner definitions
        >
Agda theorem proofs
        >
generated Agda declarations
        >
Mercury extraction / symbolic bookkeeping
        >
Guix orchestration
```

Mercury can construct a graph or generated file that is wrong. The system is designed so that correctness of the Agda proposition is decided at the `agda --safe` boundary rather than by Mercury.

Agda `--safe` disables postulates, unsafe OPTIONS pragmas, and `primTrustMe` among other consistency-sensitive features. The repository uses that mode as the proof gate.

## Generated-proof shape

The Guix driver no longer treats bare `refl` as a semantic error in the generated artifact. The generated file contains source-owned theorem projections, while the e-graph handles proof-plan normalization. Agda `--safe` remains the proof acceptance boundary.

## Retired discovery architecture

The post-TSTS migration removed the old TSTS discovery generator. The current tree also no longer contains the older Mercury oracle/discovery files that the previous wiki documented, including:

- `.ci/discovery/tsts_endogenous_discovery.m`
- `.ci/discovery/jaxtar_aq_discovery.m`
- `.ci/discovery/clojure_involution_compat.m`
- `oracle/mercury_oracle.m`

Likewise, there is no current `.ci/discovery/learner_theorem_egraph.m`.

The surviving TSTS theorem is still formalized in `TheoremsMonolith.agda`, but theorem existence and theorem-discovery tooling are separate concepts.

## Endogenous boundary

The useful invariant for future discovery work is:

```
semantic vocabulary = extracted from canonical learner/theorem declarations
candidate representation = generated from extracted vocabulary
symbolic quotienting = generic, source-driven
proof acceptance = Agda --safe
```

A future search implementation may change its enumeration, quotienting, or scheduling strategy, but it should not reintroduce an independently authored semantic alphabet that duplicates the learner's explicit Agda surface.
