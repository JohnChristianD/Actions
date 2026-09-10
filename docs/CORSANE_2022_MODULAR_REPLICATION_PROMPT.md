# Corsane 2022 modular replication contract

This document is the repository replication contract referenced by `docs/REPLICATION_INDEX.md`.

## Authority

Agda `--safe` is the authoritative mathematical gate. External implementations are independent exact-rational cross-checks only and never certify Agda proofs.

## Modular theorem path

The canonical proof decomposition is:

`Stage01 finite algebra -> Stage02 CHAD -> Stage03 learner -> Stage04 q-projection -> Stage05 representation -> Stage06 coupled learner -> Stage07 finite archive -> Stage08 integration`.

The historical `CompleteSafe_v147.agda` monolith is a compatibility/regression surface, not the semantic source of the v151 architecture.

## v151 finite ordered target

The active v151 integration target is:

`Exotic/ERL/FullCoupled/EfficientCHAD_StoSignSGDv2_Tsallis2_v151.agda`

It omits LayerNorm, BatchNorm, BatchRenorm, floating-point proof semantics, and placeholder certificate records.

The target retains:

- Affine + CReLU representation;
- fixed-window finite Tsallis-2 sparse attention;
- L1 weight norm and 1-path norm accounting;
- dyadic coupled L2 across actor, critic, and representation blocks;
- sign-q-IDBD as the default parameter-direction update;
- beta1 = 115/128 with complement 13/128;
- dyadic meta-step 1/128;
- finite CVT-ME/OpenES antithetic mutation algebra;
- finite overestimation-bias decomposition;
- custom Munchausen correction surface;
- Pareto-efficient coupled hyperparameter mapping.

## Finite algebraic expressivity target

For an affine input of degree 1, CReLU is degree-preserving on each activation branch. Bilinear query-key scores map degree `d` to `2d`. Tsallis-2 active weights preserve that score degree on each fixed active set, and multiplication by values yields degree `3d`.

Therefore an `L`-attention-layer composition has branchwise polynomial degree bounded by `3^L` under this algebraic model. Norm bounds and dyadic coefficient restrictions constrain coefficient magnitude/path mass but do not change that degree bound.

Sign is reserved for the parameter direction after q-projection. SignReLU is not part of the polynomial core because its negative branch is rational and requires denominator/domain semantics.

## Optimizer algebra

The default learner channel is:

`IDBD meta-state -> raw direction -> q-projection -> sign(parameter direction) -> coupled L2 -> parameter state`.

Momentum is representable by finite dyadic affine recurrence; with `beta1 = 115/128`, the complementary coefficient is `13/128`. No universal fixed-step no-chattering theorem is claimed. Safe theorems concern finite branch closure, sign normal forms, bounded finite-horizon sensitivity, and invariant preservation under explicit hypotheses.

## Outer emitter and objective coupling

CVT-ME/OpenES antithetic cancellation, finite emitter-state composition, overestimation-bias decomposition, the custom Munchausen surface, and Pareto-efficient coupled-hyperparameter mapping remain finite algebraic theorem targets. No stochastic asymptotic convergence claim is inferred from finite identities.

## Oracle policy

CI exact-rational cross-checks use Haskell and Elixir. Ruby remains a local native exact-Rational oracle and is deliberately excluded from CI. Python and Ruby CI repair paths are retired.

## Replication layout

Experiment records continue to use the Corsane 2022 CSV layout referenced by `docs/MODULAR_REPLICATION_LAYOUT.csv`. Historical QD results must not be presented as newly generated data.
