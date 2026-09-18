# Imported Libraries and Algebraic Substrate

Last audited: 2026-09-19.

This page records the direct library surface used by the current canonical components and the proof substrate around them.

## Agda canonical learner

### `CanonicalLearnerMonolith.agda`

Direct imports:

- `Relation.Binary.PropositionalEquality`
- `Agda.Builtin.Nat`
- `Data.Nat`
- `Data.Fin`
- `Data.Fin.Properties`
- `Data.Nat.DivMod`
- `Data.Product`
- `Data.Empty`

Roles:

| Import | Role in the learner |
| --- | --- |
| `Relation.Binary.PropositionalEquality` | equality, symmetry, transitivity, congruence, substitution |
| `Agda.Builtin.Nat` | primitive natural numbers and recursion |
| `Data.Nat` | bounded arithmetic, comparisons, truncated subtraction |
| `Data.Fin` | finite carriers such as `Fin 256` and action spaces |
| `Data.Fin.Properties` | Fin/natural round-trip properties |
| `Data.Nat.DivMod` | modular remainder bounds used to construct finite values |
| `Data.Product` | binary and nested product carriers |
| `Data.Empty` | contradiction targets and impossible finite-cycle cases |

Reference: [Agda standard library 2.3](https://agda.github.io/agda-stdlib/v2.3/).

## Canonical composition theorem module

### `CanonicalLearnerTheoremsMonolith.agda`

Direct imports:

- `Relation.Binary.PropositionalEquality`
- `Agda.Builtin.Nat`
- `Data.Empty`
- `Exotic.ERL.FullCoupled.CanonicalLearnerMonolith`

The module deliberately keeps the composition layer thin. It imports the canonical implementation and proves/repacks equations around that implementation.

## Closed-loop interface

### `CanonicalClosedLoopInterface.agda`

Direct library imports include:

- `Relation.Binary.PropositionalEquality`
- `Agda.Builtin.Nat`
- `Data.Nat`
- `Data.Fin`
- `Data.Fin.Properties`
- `Data.Nat.DivMod`
- `Data.Product`
- `Data.Empty`

Internal imports:

- `CanonicalLearnerMonolith`
- `CanonicalGamePorts`

This is the seam where the learner becomes an explicit environment/agent system.

## Faithful finite-game variants

### `CanonicalFaithfulGameVariants.agda`

Direct library imports:

- `Relation.Binary.PropositionalEquality`
- `Agda.Builtin.Nat`
- `Data.Fin`
- `Data.Nat.DivMod`
- `Data.Product`
- `Data.Empty`
- `CanonicalGamePorts`

The exact map predicates are built from finite natural-number cases and bounded comparison.

## General theorem substrate

### `GeneralFullCoupledLearnerMonolith.agda`

The general learner substrate uses the built-in natural-number and finite libraries plus list, product, relation-bundle, sorting, and lexicographic-order modules.

Its imported algebraic machinery is broader than the canonical monolith because it supports generic theorem packaging.

### `GeneralFullCoupledTheoremsMonolith.agda`

The general theorem module imports equality, natural/integer arithmetic, finite carriers, products, lists, sorting, permutation, total-order sorting, and the general learner monolith.

The Mercury JAxtar A/Q certificate lives in this theorem source.

## Mercury CI / verifier layer

The migration replaces the old Haskell theorem and discovery scripts with Mercury modules under:

- `.ci/check_forbidden_theorems.m`
- `.ci/discovery/prune_redundant_components.m`
- `.ci/discovery/prune_redundant_learner_modules.m`
- `.ci/discovery/jaxtar_aq_discovery.m`
- `.ci/discovery/clojure_involution_compat.m`
- `oracle/mercury_oracle.m`

The verifier layer uses Mercury's typed module system, determinism checking, and standard library I/O/data structures.

Mercury references:
- [Mercury documentation](https://mercurylang.org/documentation/documentation.html)
- [Mercury Language Reference Manual](https://www.mercurylang.org/information/doc-release/mercury_ref/index.html)
- [Mercury Library Reference Manual](https://mercurylang.org/information/doc-latest/mercury_library_manual/index.html)

## Guix reproducibility layer

### `.guix/channels.scm`

Pins:

- Guix branch: `version-1.5.0`
- channel commit: `ac03c482b1910a1672427beaea07ddcd1d652806`

### `.guix/manifest.scm`

Declares:

- Agda 2.7.0.1
- Agda standard library 2.3
- Mercury 22.01.4
- Python 3.11
- Guile 3.0
- Git

The Guix channel specification fixes the package graph more tightly than a manifest alone. This matches Guix's documented reproducibility model.

References:
- [GNU Guix Reference Manual](https://guix.gnu.org/manual/en/guix/)
- [GNU Guix Cookbook: reproducible profiles](https://guix.gnu.org/cookbook/en/)

## Algebraic-structure note

The canonical learner does not presently rely on generic `Algebra.*` interfaces.

Instead, structure is represented concretely:

- finite carrier: `Fin 256`;
- products: `Data.Product`;
- data constructors: `Signed`, `HardSign8`, `Phase4`;
- records: state/kernel/certificate records;
- endomorphism composition: `GRUAction`;
- associativity and equality laws: propositional equality;
- contradiction: `⊥`.

The standard library does contain generic algebraic consequences and definitions, but those abstractions are not the current dependency surface of the canonical learner. This keeps the active proof boundary concrete and small.
