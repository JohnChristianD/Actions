# Sign-q-IDBD CI and Composed Theorem Migration

## Goal
Make sign-q-IDBD the default finite-ordered learner variant, add a kernel-checkable composed-sign theorem with the existing norm/dyadic-L2/fixed-window transformer/Pareto mapping structure, and remove Python/Ruby repair infrastructure without weakening the authoritative Agda gate.

## Architecture
The repository will have two layers. The canonical theorem layer is a small self-contained `--safe` Agda module for finite ordered composition. It exposes sign-q-IDBD, optional per-feature momentum, finite path/L2 invariants, fixed-window hard attention, dyadic coupled L2, finite Pareto hyperparameter mapping, and a composed double-sign branch. `CompleteSafe_v147.agda` remains only as a compatibility/kernel surface while it is repaired and checked; it is not the semantic source of new theorem claims.

CI repair/normalisation is collapsed to an Elixir script plus an Agda checker. The Elixir script is deterministic, idempotent, and source-preserving except for explicitly named mechanical namespace repairs. The Agda checker is the authoritative semantic gate. Historical Python/Ruby repair workflows and helper scripts are removed rather than kept as fallback mutation paths.

## Learner semantics

The default update path is:
`IDBD meta-state -> raw IDBD direction -> q-projection -> parameter-direction sign -> coupled dyadic L2 -> weights`.

The optional momentum extension is feature-wise and occurs after q-projection and before the parameter-direction sign. It does not sign beta, trace, or meta-state. The theorem therefore preserves the intended IDBD semantics while exposing momentum as a separate finite state component.

The sign channel is treated as a branch constructor with an explicit zero case. The theorem does not claim universal no-chattering; it records the finite eventual-sign-stability implication and leaves stronger dynamical claims conditional on a supplied sign-separation certificate.

## Representation semantics

The canonical representation branch is non-LayerNorm and uses finite-width hard attention rather than transcendental softmax. Positional information is represented by a finite table. The composed-sign theorem applies the same finite path-norm and dyadic-L2 invariants to two sequential sign activation layers.

## Hyperparameter and outer-loop semantics

The finite Pareto mapping is retained as a certificate over a finite set of coupled hyperparameter records and objective tuples. It proves only finite dominance/maximality facts supplied by the certificate; it does not perform statistical fitting or historical data analysis.

## Interpolation and conjecture boundary

CI interpolation is represented algebraically as finite branch/interpolation witnesses and can generate candidate conjecture records from already-certified finite invariants. Generated conjectures are never promoted to theorems without an Agda proof term.

## Completion gate

The branch is mergeable only after fresh GitHub Actions runs show green authoritative `agda --safe` checks, exact oracle checks, and repository hygiene checks. Squash merge is used. The final state must have no open pull requests for this repository and no active Ruby/Python repair or CI files in the migrated surface.
