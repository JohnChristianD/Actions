# Efficient-CHAD v150 LayerNorm-free theorem target

This target is the canonical finite-ordered algebra branch for the v150 Efficient-CHAD architecture.

## Canonical composition

`Affine -> CReLU -> finite-window QK score -> Tsallis-2 sparse equilibrium -> weighted value sum`

with learner boundary

`IDBD direction -> q-projection -> standard magnitude-aware q-IDBD -> dyadic coupled L2`.

Parameter-direction sign is an optional ablation only. LayerNorm is excluded.

## Norm invariants

For a finite weight matrix `W`, the representation certificate carries the entrywise L1 weight norm

`||W||_1 = sum_ij |W_ij|`.

For a finite matrix chain the certificate carries the one-path envelope

`P_1 = 1^T |W_L| ... |W_1| 1`.

CReLU has branch slopes in the finite set `{0,1,-1}` and therefore does not introduce an amplification factor above one into these absolute-value envelopes. The norm theorems are finite ordered inequalities, not real-analysis norm-limit arguments.

## CReLU branch theorem

For `CReLU(x) = (max(0,x), max(0,-x))`, carry

`cplus(x) - cminus(x) = x`

and

`cplus(x) + cminus(x) = |x|`.

On each fixed branch CReLU is affine, so it does not increase polynomial degree.

## Tsallis-2 equilibrium theorem

For finite scores `s`, the sparse equilibrium is represented by

`p_i = max(s_i - tau, 0)`

with

`sum_i p_i = 1`.

The active set is finite data. For fixed active set `A`, each active coefficient is affine in the scores and inactive coefficients are exactly zero.

Thus equilibrium, complementarity, normalization, and active-set stability are finite ordered-algebraic certificates.

## Branchwise polynomial-degree theorem

If the incoming fixed-branch representation has polynomial degree `d`, affine Q/K/V maps have degree at most `d`; the QK score has degree at most `2d`; Tsallis coefficients have degree at most `2d`; and coefficient-times-value has degree at most `3d`.

Therefore

`D(0) = 1` and `D(k+1) = 3 D(k)`,

so

`D(k) = 3^k`.

This is a branchwise upper bound, not a claim of global arbitrary-polynomial universality.

Dyadic coupled-L2 normalization, L1 weight bounds, and one-path bounds constrain coefficient magnitude and sensitivity; they do not change this degree recurrence unless an additional data-dependent division operation is introduced.

## Efficient-CHAD sensitivity theorem target

For a fixed CReLU branch and fixed Tsallis active set, the primal and pullback maps are finite compositions of affine maps, products, comparisons, max/positive-part branches, and finite sums. The sensitivity certificate therefore has the form

`Sensitivity <= finiteCoefficientEnvelope`

with the envelope assembled from the representation L1 bound, one-path bound, and normalized nonnegative Tsallis routing weights.

No mean-value theorem, topology, limiting argument, or full real-analytic semantics is required.

## q-IDBD theorem

The canonical learner retains the q-projected direction magnitude. The optional signed learner applies a sign only after q-projection.

`q-IDBD` therefore refines the signed direction-only quotient; it is not extensionally equal to sign-q-IDBD before quotienting update magnitudes.

## Double-sign extension

When the forward representation is sign/CReLU-partitioned and a parameter-direction sign branch is enabled, the finite state partition is

`forward-branch × Tsallis-active-set × update-sign-branch`.

The two sign mechanisms operate on different state spaces and are not algebraically redundant. With CReLU plus standard q-IDBD, forward and update magnitude are retained, while the optional update sign remains a finite branch quotient.

## Composite preservation target

The v150 integrated invariant is

`CReLU reconstruction ∧ CReLU magnitude ∧ L1 bound ∧ 1-path bound ∧ Tsallis normalization ∧ Tsallis complementarity ∧ q-projection idempotence ∧ dyadic-L2 law ∧ branchwise sensitivity bound ∧ degree recurrence`.

The target theorem is one-step invariant preservation followed by finite-horizon induction.

## Oracle and CI policy

Agda `--safe` remains the mathematical authority. Haskell, Elixir, and native Ruby use exact Rational arithmetic as independent finite cross-checks only. They cannot promote a theorem to kernel-proved status.

Python is not an active CI language for v150. LayerNorm is not an active v150 theorem component.
