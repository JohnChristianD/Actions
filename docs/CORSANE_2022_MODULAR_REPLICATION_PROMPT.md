# Corsane 2022 modular replication contract

This document is the repository replication contract referenced by `docs/REPLICATION_INDEX.md`.

## Authority

Agda `--safe` is the authoritative mathematical gate. External implementations are independent exact-rational cross-checks only and never certify Agda proofs. Elixir is the deterministic normalization/hygiene layer; Haskell and local-native Ruby are independent exact-rational reference implementations, with Ruby excluded from CI.

## Modular theorem path

The canonical proof decomposition remains:

`Stage01 finite ordered algebra -> Stage02 CHAD -> Stage03 learner -> Stage04 q-projection -> Stage05 representation -> Stage06 coupled learner -> Stage07 finite archive -> Stage08 integration`.

The historical `CompleteSafe_v147.agda` monolith is compatibility/regression material, not the semantic source of the v151 architecture. The new v151 self-contained file is a controlled closure target and must remain semantically consistent with the modular path.

## v151 finite ordered target

The active integration target is:

`Exotic/ERL/FullCoupled/EfficientCHAD_StoSignSGDv2_Tsallis2_v151.agda`

It omits LayerNorm, BatchNorm, BatchRenorm, floating-point proof semantics, placeholder certificate records, Python CI/repair, Ruby CI/repair, and stale double-sign workflow surfaces.

The target retains:

- Affine + CReLU representation;
- fixed-window finite Tsallis-2 sparse attention with finite positional tables;
- exact L1 weight-norm accounting;
- exact finite 1-path norm `1^T |W_L| ... |W_1| 1`;
- dyadic coupled L2 across actor, critic, and representation blocks;
- sign-q-IDBD as the default parameter-direction update;
- sign applied only after q-style projection;
- beta1 = `115/128`, complementary momentum coefficient `13/128`;
- dyadic meta-step `1/128`;
- optional per-feature dyadic momentum state;
- finite CVT-ME/OpenES antithetic mutation algebra with Tsallis-2 mutation/active-set target;
- finite overestimation-bias decomposition;
- custom Munchausen correction surface;
- Pareto-efficient coupled-hyperparameter mapping as a finite relation target.

## Finite algebraic expressivity target

For affine input degree `1`, every CReLU branch is affine and therefore degree-preserving. Bilinear query-key scoring maps degree `d` to `2d`. The fixed-active-set Tsallis-2 weights are affine in the scores and therefore remain degree `2d`; multiplying a weight by a value of degree `d` gives degree `3d`. Hence an `L`-attention-layer composition has branchwise polynomial degree at most `3^L` for the stated bilinear-QK/value model.

This is a branchwise degree bound, not a claim of global polynomial universality. Norm constraints restrict coefficient/path magnitude; dyadic parameterization restricts coefficient arithmetic. Neither changes the degree recurrence.

For ordinary identity/ReLU/CReLU activations, the same fixed-branch degree recurrence is retained because these activations are affine on each branch. Sign activation instead collapses the scalar feature to a finite sign alphabet and therefore does not retain the same polynomial-degree growth. SignReLU is excluded from the core because its negative branch is rational and would require denominator/domain closure rather than the current polynomial branch algebra.

## Equilibrium, sensitivity, and non-chattering targets

The primary equilibrium target is the finite Tsallis-2 active-set/KKT normal form:

`p_i = max(s_i - tau, 0)` and `sum_i p_i = 1`.

A fixed active set yields an affine normal form and a finite sensitivity/Jacobian calculation. Composition with CReLU yields a finite polyhedral region index; composition with q-projection and sign-q-IDBD yields a finite parameter-direction partition.

No unconditional infinite-horizon no-chattering theorem is claimed for arbitrary fixed-step sign dynamics. The safe theorem target is finite normal-form/idempotence, finite-horizon switch accounting, and invariant preservation; stronger no-switch results require explicit local premises.

## Optimizer algebra

The default channel is:

`IDBD meta-state -> raw direction -> q-projection -> sign(parameter direction) -> dyadic momentum -> coupled L2 -> parameter state`.

The sign is never applied to beta, trace, or meta-state themselves. Per-feature dyadic momentum is represented by affine recurrence, with beta1 `115/128`; the complementary coefficient is `13/128`. The meta-step is dyadic `1/128`.

Sign-q-IDBD is the default because the project explicitly targets a finite directional quotient after q-projection; it is not asserted to be numerically or asymptotically superior to magnitude-preserving q-IDBD without a separate theorem or experiment.

## Norm and stability algebra

The representation must carry both invariants:

`weightL1(W) = sum_ij |W_ij|`

and

`onePathNorm(W_1,...,W_L) = 1^T |W_L| ... |W_1| 1`.

CReLU has branch slopes in `{0,+1,-1}` under the signed two-channel representation convention, so it is compatible with the absolute-weight/path envelope. Tsallis-2 routing satisfies nonnegative normalized mass and therefore does not add an L1 amplification factor at the attention aggregation boundary.

The coupled regularizer is dyadic:

`L2(theta) = sum_b 2^(-k_b) ||theta_b||_2^2`.

All proof-relevant scalar hyperparameters in the finite recurrence should use exact dyadic/rational encodings. Dimensions, finite horizons, archive capacities, and other structural counts remain natural numbers.

## Outer emitter and objective coupling

CVT-ME/OpenES retains the finite antithetic mutation law and emitter-state composition. Tsallis-2 is available as the finite sparse mutation/active-set law. The target also retains finite overestimation-bias decomposition, the custom Munchausen correction, and Pareto-efficient coupled-hyperparameter mapping. These are finite algebraic theorem surfaces, not stochastic asymptotic guarantees.

## Oracle policy

The kernel is authoritative. CI exact-rational cross-checks use Haskell and Elixir. Ruby may remain as a local native exact-Rational oracle but is not CI. Python and Ruby repair/CI workflows are retired. Independent oracles may detect discrepancies but cannot rewrite, weaken, or certify Agda theorem statements.

## Closure policy

There are no placeholder certificate records. A theorem is considered closed only when its actual Agda term type-checks under `--safe` or when the repository explicitly labels it a target requiring a future proof obligation. “Certificate” is therefore documentation of a proof obligation, not a substitute for the proof.

No historical QD result may be presented as newly generated data. Experiment records continue to use the Corsane 2022 CSV layout referenced by `docs/MODULAR_REPLICATION_LAYOUT.csv`.
