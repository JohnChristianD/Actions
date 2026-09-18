# Imported Libraries and Algebraic Substrate

Last audited: 2026-09-19.

## Canonical learner

### `CanonicalLearnerMonolith.agda`

Direct library surface:

- `Relation.Binary.PropositionalEquality`
- `Agda.Builtin.Nat`
- `Data.Nat`
- `Data.Fin`
- `Data.Fin.Properties`
- `Data.Nat.DivMod`
- `Data.Product`
- `Data.Empty`

The canonical learner uses concrete finite carriers, products, records, finite data declarations, and propositional equality.

## Canonical theorem monolith

### `TheoremsMonolith.agda`

Direct imports:

- `Relation.Binary.PropositionalEquality`
- `Agda.Builtin.Nat`
- `Data.Empty`
- `Data.List.Base`
- `CanonicalLearnerMonolith`

The theorem monolith is intentionally compact at the import boundary. It proves composition over the existing learner functions instead of rebuilding the implementation.

## Closed-loop interface

### `CanonicalClosedLoopInterface.agda`

Uses:

- propositional equality;
- natural numbers;
- finite action/state indices;
- product records;
- finite division/remainder utilities;
- `CanonicalLearnerMonolith`;
- `CanonicalGamePorts`.

## Mercury verifier surface

Active Mercury sources:

- `.ci/check_forbidden_theorems.m`
- `.ci/discovery/jaxtar_aq_discovery.m`
- `.ci/discovery/prune_redundant_components.m`
- `.ci/discovery/prune_redundant_learner_modules.m`
- `.ci/discovery/clojure_involution_compat.m`
- `oracle/mercury_oracle.m`

The old Python finite-search implementation has been removed.

## Guix reproducibility layer

### `.guix/channels.scm`

- Guix branch: `version-1.5.0`
- channel commit: `ac03c482b1910a1672427beaea07ddcd1d652806`

### `.guix/manifest.scm`

- Agda 2.7.0.1
- Agda standard library 2.3
- Mercury 22.01.4
- Guile 3.0
- Git

Python is no longer part of the reproducible verification environment.

## Algebraic structure

The canonical source is concrete rather than class-heavy:

- `Int8` is carried through `Fin 256`;
- small vectors use `Data.Product`;
- closed alternatives use Agda `data` declarations;
- state and certificates use records;
- `GRUAction` gives explicit endomorphism composition;
- laws use propositional equality;
- impossibility uses `⊥`.

The current architecture does not require JVM, Elm, PureScript, JavaScript, TypeScript, or Haskell abstractions.
