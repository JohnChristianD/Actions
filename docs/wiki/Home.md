# Actions: Agda Semantics and Theorem Wiki

This repository documents the coupled ERL/GRU/F4/reservoir formalization directly from the Agda source.

> Wiki availability note: the separate GitHub \`Actions.wiki\` repository is not exposed by the current GitHub connection. These pages are therefore kept as an in-repository wiki mirror under \`docs/wiki/\` rather than pretending that the hosted wiki was updated.

Documentation baseline: commit \`09e263b77bb92a3a0d6123382edee895bc73b179\`.

## Canonical semantic surface

The canonical proof target is the six-state F4 learner in \`CanonicalCoupledF4Learner.agda\`. It uses the general learner monolith for action selection, Munchausen shaping, GRU state transition, and norm state, but replaces the old five-field F4 optimizer with a corrected six-field signed F4 state.

The canonical gate is \`sign(x)\`, implemented by \`canonicalSign = L.hardSignGate\`. It is state-independent and input-dependent.

The canonical F4 global L2 term is the parameter-level coupled term βθ · θfull. It is not a separate optimizer-state coordinate.

## License

This repository is distributed under the **GNU Affero General Public License v3.0 only**. See \`License.md\` for the downstream-distribution and network-interaction implications and the fixed-version policy.

## Pages

- \`Canonical-Semantics.md\`: actual state, arithmetic, GRU gate, F4 transition, and coupled learner composition.
- \`Theorem-Index.md\`: theorems that are kernel-checked, conditional certificate records, and what each result does not prove.
- \`Imports.md\`: exact imports used by the core modules at the documentation baseline.
- \`Syntax-Hygiene.md\`: namespace, binder, \`with\`, and public-field naming rules used to prevent Agda 2.8 collisions.
- \`Verification-Status.md\`: current Safe Agda closure status and the remaining generalized-monolith blocker.
- \`License.md\`: AGPL-3.0-only licensing policy and canonical license references.

## Semantic warning

There are two F4 definitions in the repository.

The canonical definition is the six-state signed/clipped/scaled kernel. The older \`GeneralFullCoupledLearnerMonolith\` F4 definition is a legacy five-state modular-code kernel with \`l2Global\` stored as a state field. The latter is still imported by several generic theorem modules and must not be described as the canonical optimizer semantics.

Likewise, piecewise-rational theorem machinery in the theorem monolith is a separate symbolic representation. It is not the canonical GRU activation.
