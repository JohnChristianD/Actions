# Theorem-first finite ERL/EA replication wiki

Authority: Agda `--safe`.

## Canonical composition

The active representation theorem is now ordered as

`E -> dyadic RoPE (Walsh-Rademacher) -> sparsemax -> frozen Haar -> specialized GRU -> Pi`.

There is no standalone pointwise forward-activation layer and no MLP between sparsemax and the recurrent representation. The only nonlinear activation maps retained in the representation path are the GRU's internal gates.

The GRU uses

`g_z = 0.5 * (1 + softsign)`
`g_r = 0.5 * (1 + softsign)`
`h~  = signReLU`

so the nonlinearities are sequentially recurrent rather than independent feed-forward layers. The finite midpoint operator is an Int8 CHAD boundary; its concrete exact semantics must be supplied by the implementation witness.

## Recurrent exploration noise

A standard GRU has six affine matrices: three input matrices and three recurrent matrices. The retained exploration perturbation is restricted to the three recurrent matrices

`U_z, U_r, U_h`.

Thus the answer is three recurrent noise matrices, not six. Bias vectors are separate parameters and are not counted as matrices.

For the concrete theorem carrier with hidden width `2`, the persistent noisy recurrent state has

`3 * 2 * 2 + 2 = 14`

Int8 coordinates: twelve recurrent-matrix entries plus two hidden-state entries. Before optimizer or auxiliary coordinates are adjoined, the carrier therefore has `256^14` possible states. The general hidden-width `d` form is `3d^2 + d` Int8 coordinates.

## Global optimizer remains coupled

The recurrent theorem surface retains the global optimizer and global L2 regularization as one coupled optimization boundary. The optimizer ledger also carries the global F4-Int(U) input law and softsign-q-IDBD boundary. No local optimizer substitution is introduced merely because recurrence was added.

The GRU and sparsemax attention are the nonlinear components carrying the paired L1/path-one norm obligations. Global L2 remains a separate global regularizer and is not absorbed into the recurrent gate definition.

## Dyadic positional and frozen features

RoPE is retained structurally as the positional-composition boundary, but Fourier/trigonometric phase coordinates are not required by the finite theorem surface. The canonical dyadic form uses a frozen Walsh-Rademacher basis and exact dyadic signed actions.

The Haar stage is frozen before the GRU. Exact decorrelation is a theorem field of that frozen feature layer rather than an empirical covariance claim.

Frozen random features remain frozen theorem witnesses; no additional named stochastic-feature construction is inserted into the active representation path.

## Möbius composition

`Exotic/efficient_chad/GRUGatedComposition.agda` places the CHAD and Möbius theorem boundary inside the GRU gates. The composition law is pointwise in the sequential forward value: the outer recurrent gate receives the actual finite output of the preceding gate.

`Exotic/efficient_chad/GRURecurrentMobius.agda` adds the new recurrence theorem class. A recurrent window is a finite homogeneous action and window composition is associative. The exact identity

`(A * B) * C = A * (B * C)`

is kernel-checked for the finite action composition, giving the algebraic basis for parallel associative scan over recurrent windows/depths.

This is stronger algebraic structure than a one-step feed-forward composition theorem because the recurrence is now a finite action monoid/semigroup under sequential composition. It is not automatically a stronger state-reachability theorem until an explicit projection/lift theorem connects the recurrent state to the previous coupled learner state.

## Theorem ordering

The previous structural relation

`OpenES < MR15 < NoisyNet`

continues to describe the old finite factor chain. The GRU recurrence introduces a new class above that chain only after a concrete factor is supplied from the prior coupled state into the GRU state.

The current safe theorem is therefore:

`old feed-forward factor class  <  finite recurrent-Möbius class`

as an algebraic-structure statement, while

`NoisyNet < GRU-NoisyNet`

remains conditional on the missing proper projection/lift between those concrete state carriers. The repository deliberately does not fake that bridge.

## Scan theorem and recurrent depth

Parallel scan is exact whenever each recurrent window has a finite homogeneous-coordinate action witness and window multiplication is associative. A balanced tree can therefore precompute recurrent products without changing the serial recurrence semantics.

The theorem applies per finite recurrent window/depth. It does not require an infinite recurrent tape.

## Mamba / SSRN relation

The scan theorem is in the same broad algebraic family as input-dependent state-transition scans: sequential state evolution is compiled into associative products of finite transition operators. That is Mamba/structured-state-space-like at the theorem level, but the present object remains a GRU recurrence with finite Int8 Möbius witnesses; it is not asserted to be a Mamba or SSRN implementation.

## Infinite-width and tropical limits

The canonical mathematical authority remains finite Int8. Consequently, a literal infinite-input, infinite-width, or real-valued limit is not admitted as a primitive theorem object.

The admissible derived forms are finite dyadic tropical/idempotent shadows and finite-width diagonal Jacobian factorization theorems. Any genuine limit theorem would require a separately constructed finite-family/limit object and cannot be smuggled in through an informal analytic limit.

## Norm, decorrelation, and derivation ledger

The retained derivation stack is

`Tom Smeding norm-pair -> global L2 -> global F4-Int(U) -> softsign-q-IDBD -> Efficient-CHAD -> GRU recurrence -> Möbius window composition -> sparsemax -> exact decorrelation -> frozen Haar/Walsh-Rademacher features -> dyadic finite exploration`.

Each stage is a theorem interface. None is accepted merely because an external implementation uses the corresponding name.

## Probability law

Flat Dyadic remains the sole active probability law. It has exact denominator `256`, positive zero support, positive `±1` support, symmetry, constant profile, finite unimodality, aperiodicity, and full additive `Z_256` generator support.

The earlier non-flat law frontier is retired from the active theorem surface. No law is ranked by statistics.

## Current emergent theorem

The current canonical theorem is therefore a finite recurrent composition theorem:

`flat dyadic law`
`+ dyadic Walsh-Rademacher positional action`
`+ sparsemax attention`
`+ frozen Haar decorrelation`
`+ internal GRU {0.5*(1+softsign), signReLU}`
`+ three-matrix recurrent noise`
`+ global optimizer + global L2`
`+ Efficient-CHAD`
`+ pointwise sequential Möbius composition`
`+ associative recurrent window products`

with Agda `--safe` as the acceptance oracle.

No empirical ranking or data analysis is used.
