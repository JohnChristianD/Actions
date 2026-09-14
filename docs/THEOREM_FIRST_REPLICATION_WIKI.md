# Theorem-first finite ERL/EA replication wiki

Authority: Agda `--safe`.

## Canonical composition

The active representation theorem is ordered as

`E -> dyadic RoPE (Walsh-Rademacher) -> sparsemax -> frozen Haar -> specialized GRU -> Pi`.

There is no standalone pointwise forward-activation layer and no MLP between sparsemax and the recurrent representation. The only nonlinear maps retained in the representation path are internal GRU gates:

`g_z = 0.5 * (1 + softsign)`
`g_r = 0.5 * (1 + softsign)`
`h~  = signReLU`.

## GRU perturbation methods

`Exotic/ERL/Exploration/GRUPerturbationMethods.agda` is the active method theorem class:

`GRU-OpenES`, `GRU-MR15`, `GRU-NoisyNet`.

All three currently use the same finite `GRUNoisyNetState` carrier and fresh-target recurrent-noise shell. Consequently all three have exact irreducibility, self-loop, period-one, and aperiodicity witnesses.

A strict ranking is not inferred from the names of the methods. It requires explicit method-specific state maps, projection/lift/retraction, and a proper fiber witness. The old `OpenES < MR15 < NoisyNet` theorem has been removed rather than relabeled.

## Recurrent exploration noise

A standard GRU has six affine matrices: three input matrices and three recurrent matrices. The retained exploration perturbation is restricted to `U_z`, `U_r`, and `U_h`.

For hidden width `2`, the persistent noisy recurrent state has `3 * 2 * 2 + 2 = 14` Int8 coordinates. Before optimizer or auxiliary coordinates are adjoined, the finite carrier therefore has `256^14` states. The general hidden-width `d` count is `3d^2 + d`.

## Aperiodicity

The finite theorem schema now exposes `Aperiodic` explicitly as the irreducible-plus-self-loop witness. The GRU fresh-target shell reaches every target state in one step and can target its source state, giving the aperiodicity witness exactly and finitely.

No limiting or environment-dependent statistical theorem is involved.

## Dyadic positional and frozen features

RoPE and Haar are structurally complementary rather than arithmetically redundant.

Dyadic RoPE supplies positional action: a finite Walsh-Rademacher signed/permutation law that moves or reindexes coordinates before attention. Haar supplies a fixed linear transform and an exact decorrelation witness after sparse support selection. They can both be finite and dyadic, but they certify different maps and commute only under additional concrete hypotheses; neither is redundant merely because both are linear/finitary.

The Haar stage is frozen before the GRU. Exact decorrelation is a theorem witness, not an empirical covariance result.

## Transformer-like algebraic class

The architecture is close to the Transformer-family theorem surface because it combines positional encoding, sparse attention, and a representation block operating over a context window. With recurrence, however, the exact algebraic kernel is a finite state-transition/action composition rather than a standard parallel self-attention theorem.

The recurrence can provide arbitrarily many finite windows semantically, but the canonical theorem remains finite: each concrete window has a finite action witness and products reassociate exactly. That is the right proof-level relation to JAX state-transition/sequence models and associative state-space scans, without claiming a literal Transformer, Mamba, or SSRN implementation.

## Möbius composition and scan

`Exotic/efficient_chad/GRUGatedComposition.agda` contains the sequential gate CHAD/Möbius witness boundary.

`Exotic/efficient_chad/GRURecurrentMobius.agda` proves associative finite window composition, giving the exact algebraic kernel for parallel scan. A concrete full-GRU matrix-product theorem still requires a homogeneous/action witness for the actual bilinear update/reset recurrence.

## Global optimizer, norms, and actor-critic

`GRUComposition` keeps the global optimizer and global L2 boundaries coupled to the recurrent learner. The GRU and sparsemax-side components retain the paired L1/path-one obligation surface, while global L2 stays global.

The repository has an Int8 shared actor/critic construction. The GRU boundary now names an explicit DPG-update proof obligation, because an Int8 carrier by itself does not prove the DPG update semantics.

## Probability law

Flat Dyadic remains the sole active law: exact uniform weight `1` over the `256` Int8 residues. Its algebraic cleanliness comes from constant full support, exact normalization, positive zero/self-loop support, and positive unit moves—not from strong unimodality as a separate ingredient.

A weak or strong unimodality predicate is a derived property here, not the source of the finite collapse.

## Pruned surfaces

The standalone softsign-gated representation, standalone pointwise activation helper, softsign-specific pointwise Möbius bridge, legacy Noisy-Net toy state, and legacy strict-factor theorem modules have been removed from the active tree.

No empirical ranking or environment-dependent statistical theorem is used.
