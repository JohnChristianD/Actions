# Tom Smeding Efficient-CHAD audit

Pinned upstream commit: `0be45ee9e7498a69c083a25ac9ba29bba4431a71`.

The canonical CI clones this exact commit and checks the presence of `chad-cost.agda` and `chad-preserves-primal.agda`.

## Dependency result

The checked upstream proof is `--safe`, but it is not a no-standard-library proof. The import audit observed standard-library families including:

- `Data.List`, `Data.List.Properties`
- `Data.Nat`, `Data.Integer`, `Data.Integer.Properties`, `Data.Integer.Solver`
- `Data.Fin`, `Data.Vec`, `Data.Product`, `Data.Sum`, `Data.Bool`, `Data.Empty`
- `Function.Base`
- `Relation.Binary.PropositionalEquality`, `Relation.Nullary`

The source also has internal dependencies through `spec`, `setup`, `spec.LACM`, `spec.linear-types`, `lemmas`, `eval-sink-commute`, and `chad-preserves-primal`.

## No-stdlib probe

CI runs `agda --safe chad-cost.agda` with an isolated empty library registry. The observed failure is `Library 'standard-library' not found`, so the probe is deliberately recorded as an expected incompatibility, not as a proof failure of the upstream project.

## Pruning decision

Do not copy the upstream implementation into the canonical no-stdlib tree. Retain the pinned source as an audited external reference. The first future port boundary is the semantic CHAD kernel around `chad-cost.agda` and `chad-preserves-primal.agda`; their transitive standard-library dependencies must be replaced by builtin-only equivalents before admission.

The local v164 core therefore remains independent of that dependency graph. It expresses only the finite algebraic interfaces needed by the learner and leaves the upstream CHAD proof as a separately audited reference.
