# Adaptive sparsemax action-domain redesign — 2026-09-23

The canonical sparsemax/action layer no longer uses `Fin n` as its action domain.

Decision:
- Action identifiers are `Nat`.
- The finite evaluation domain is an explicit `List Nat` carried by `ActionSpace`.
- Scores and counts are total functions over `Nat`, so action labels are not coupled to a cardinality parameter.
- Sparsemax sorting and support search operate only on the supplied candidate list.
- The learner no longer defines canonical 2-, 4-, or 64-action defaults.
- `Integer`/the existing `Int8`-over-`ℤ` representation remains the arithmetic carrier; it is not used to enumerate the action domain.
- A fallback `witness : Nat` is supplied by each `ActionSpace` for the empty/no-positive-support case.

This keeps exact sparsemax computation finite without making finiteness a type-level hyperparameter. Adaptivity is therefore a data property of the candidate list rather than a hardcoded `Fin n` cardinality.

Compatibility note:
The learner state/kernel still carry a type-level tag parameter so existing theorem interfaces can be migrated incrementally. That tag is no longer an action cardinality and must not be interpreted as one.

Finite POMDP, Walrasian, transport, and automata theorem surfaces remain separate theorem-monolith material. Their intended promotion path is through the repository's theorem e-graph/import layer; they are not deleted merely because the canonical sparsemax/action domain is no longer finite-indexed.

Auto-merge:
The Dhall `AutoMerge` lane now invokes `gh pr merge --auto` without selecting `--rebase`. GitHub can therefore use the repository/merge-queue policy rather than the lane hard-coding a merge method.
