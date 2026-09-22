# Actions — formal theorem graph and canonical learner

This repository is a small, executable formal-methods stack for composing theorem declarations, learner semantics, and dependency graphs across Agda and Mercury.

## Canonical proof surface

- `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda` — canonical learner state, transition, recurrent, sparsemax, Haar, observation, and invariance primitives.
- `Exotic/ERL/FullCoupled/TheoremsMonolith.agda` — the single public theorem facade built on that learner source.
- `.ci/actions_ci.dhall` — typed CI-lane generator. It orchestrates checks; it is not a proof authority.
- `.ci/discovery/` — Mercury theorem/e-graph discovery and graph-search programs.

Agda `--safe` is the authoritative proof gate. Agda documents `--safe` as disabling postulates and other features that can undermine consistency; imported modules must also satisfy the safety constraints. citeturn0search0turn0search10

## Emergent endogenous theorem

The latest graph-composition pass exposes a new endogenous closure surface:

`canonical-learner-replacement-closure-theorem`

It packages the existing list-composition law for an arbitrary finite list of the repository's existing `LearnerReplacement` constructors: `normReplacement` and `optimizerReplacement`. The proof recursively composes the already-established NormPair and optimizer invariance laws. It introduces no new learner primitive or search-specific axiom.

The stronger combined surface is `canonical-haar-sparsemax-full-state-closure-theorem`. Its dependency shape is:

`fixed sparsemax counts` → `integer Haar linearity/orthogonality` → `full-state NormPair invariance` → `full-state optimizer invariance` → `finite learner-replacement closure` → `Haar + sparsemax + full-state closure`.

Other exact composition surfaces include recurrent-prefix monoid homomorphism, finite direct-product closure, exact observation/readout boundaries, state-isomorphism transport, and architecture-preserving canonical RNN-LM identity.

## What the invariance theorem actually says

The current formal invariance is primarily a canonical learner interface theorem, not a theorem about every modern sequence architecture.

The canonical learner explicitly models a GRU/RNN-style recurrent state together with F4/L2, count/policy, q-log, and endogenous feedback channels. Its full-state policy is invariant under replacement of the NormPair and optimizer components because the canonical policy reads the Watkins/LCB count/critic path rather than those replaced fields.

The theorem therefore applies directly to the formalized canonical RNN/GRU learner.

It does not currently establish the same theorem for arbitrary Transformers, Mamba, S4/S5, or other state-space/recurrent architectures. To claim transfer, an architecture must first be represented by the relevant state-transition/observation interface and the required invariance premises must be proved for that representation.

Transformer and SSM literature already contains substantial symmetry and equivalence theory. State-space duality explicitly connects Transformer and SSM computations, and recent work studies permutation or gauge symmetries in Transformer and state-space architectures. citeturn1academia12turn1academia13turn1search16

## Thesis / literature position

It would be too strong to call the current theorem globally unique in the literature.

A defensible thesis claim is narrower: this repository develops a machine-checked, source-derived composition of fixed sparsemax, an integer Haar transform, and full-state learner-replacement invariance, with automated Mercury dependency/e-graph search used to expose the composition and Agda `--safe` used as the proof authority.

The potentially distinctive contribution is the combination and formalization pipeline, not the generic idea of invariance itself. Neural-network parameter symmetries, Transformer gauge symmetries, and invariant/equivariant sequence architectures are established research topics. citeturn1search17turn1search19turn1search20

A thesis should phrase novelty as a research hypothesis to be tested by a systematic related-work review, rather than as a fact established by this repository alone.

## Architecture scope

| Architecture family | Current status |
| --- | --- |
| Canonical GRU/RNN learner | Formalized directly |
| Generic recurrent networks | Generic prefix/endomorphism laws are formalized |
| Transformers | Not instantiated by the current learner theorem |
| Mamba / selective SSMs | Not instantiated by the current learner theorem |
| S4/S5-style recurrent scans | Shared abstract scan algebra is formalized; this is not a claim that the canonical learner is literally S4/S5 |
| Other SSRN/SSM variants | Require an explicit state/interface instantiation and proof of the required invariance premises |

The generic recurrent laws are deliberately separated from architecture-specific claims. That prevents an abstract monoid law from being mislabeled as a theorem about a particular neural architecture.

## Safe compilation and CI status

The repository uses Agda `--safe` for both monoliths. A successful CI run is required before a newly added theorem is described as CI-verified.

The most recent run for commit `422a39c516b568a1e66171f0feeea4df8672ac0c` failed, not green. Its Agda job hit a Nix/flake lock-file race before the canonical monolith checks could establish a clean proof result. Its Mercury job separately failed because `.ci/discovery/theorem_graph_search.m` contained a duplicate implementation-side declaration of `all_scores_non_decreasing/2`.

Those are CI failures, not proof of theorem invalidity. The repair removes the Mercury duplicate declaration and serializes Dhall generation/execution inside one Nix development process so the two sides do not race on the local flake lock.

Do not treat a cancelled predecessor run as a theorem result. Workflow concurrency is configured with `cancel-in-progress: false`, so newer pushes do not intentionally cancel older runs through that concurrency setting.

## Verification contract

The intended green state is:

1. `CanonicalLearnerMonolith.agda` passes Agda `--safe`.
2. `TheoremsMonolith.agda` passes Agda `--safe`.
3. Mercury discovery builds and validates its dependency graph.
4. The semantic contract contains every required canonical theorem symbol.
5. No generated semantic lookup table becomes a hidden proof authority.
6. Documentation describes theorem premises and limitations without upgrading benchmark specifications into proved theorems.

Agda's documentation emphasizes that `--safe` rejects mechanisms such as postulates, incomplete proofs, disabled termination checking, and other potentially inconsistent features. citeturn0search0

## Research boundary

This project distinguishes three layers:

- **Semantics:** Agda definitions and proofs.
- **Discovery:** Mercury graph search/e-graph composition over declarations that already exist.
- **Orchestration:** Dhall-generated CI scripts.

Discovery can surface a promising endogenous composition, but only the Agda proof term establishes its formal truth. This separation is intentional and prevents a graph-search result from becoming an unsupported theorem claim.

## References

- Agda Safe Agda documentation.
- Dao & Gu, *Transformers are SSMs: Generalized Models and Efficient Algorithms Through Structured State Space Duality*.
- Recent work on permutation-equivariant state-space models and Transformer symmetry/gauge structure is relevant background, but does not by itself establish the repository's exact theorem.
