# Exact Int8 Transformer Learner Specification

## Purpose

Create one canonical finite learner whose executable semantics, algebraic proofs, VJP, and Agda2HS output all come from the same `--safe` Agda definitions.

## Canonical composition

The representation is ordered exactly as:

`phi_xi = Pi o GateNN o sR2 o sR1 o Fastfood o Pyr^top-k o RoPE o E o T`

No nonlinear stage may be commuted merely because another implementation happens to expose a different order. Commutation claims require an explicit equality proof. Permutation-only reordering is permitted only through a typed permutation theorem.

The gating layer uses:

`W3 = mu3 + sigma3 * epsilon`, with finite triangular noise `epsilon` supported on `[-15,15]`.

Noisy Nets are the only exploration mechanism and noise occurs only at the gating layer.

## Learner update

The learner state contains all learnable quantities and all discrete memory needed by the transition:

- shared representation parameters `xi`
- critic parameters `theta`
- actor parameters `psi`
- gate parameters `mu3` and dyadic `sigma3`
- sigma-delta residuals for the learnable update coordinates
- TD(lambda) traces/state
- dyadic step exponents, bounded below by `ell_min = 0`

One transition reads one immutable snapshot of the complete state, performs the primal forward pass and all VJPs from that snapshot, then performs one synchronous parameter commit.

The canonical backup is standard TD(lambda) with a hard max. There is no replay and no minibatch aggregation.

## Arithmetic

All learner arithmetic is finite Int8 plus dyadic bookkeeping. There are no transcendental functions, irrational constants, softmax, Munchausen return shifts, Tsallis-2 distributional targets, or other omitted mechanisms.

## VJP authority

The learner uses explicit finite VJP operators. A VJP node carries its primal result and pullback. The proof surface establishes:

1. primal preservation of each primitive used by the canonical learner;
2. composition/chain law of pullbacks;
3. equality between the composed VJP and the learner's committed update.

No second autodiff implementation may be promoted to mathematical authority.

## F4-Int update

The update separates each learnable coordinate into a quantised coordinate and residual state. The residual carries sub-ULP information, but residual accumulation is not by itself an irreducibility theorem. Quantised movement is proved separately.

The dyadic scale exponent has an explicit floor `ell >= 0` so the canonical step scale never vanishes through exponent underflow.

## Ergodicity claims

The following are distinct:

1. `D_tri` support generates the local Int8 additive moves.
2. The actual joint learner transition is irreducible.
3. The actual joint transition is aperiodic.
4. Finite irreducibility gives recurrence; finite irreducibility plus aperiodicity gives the usual finite-chain convergence consequences.

The implementation may prove (1) unconditionally. Claim (2) requires an actual reachability proof for the complete transition and cannot be inferred from (1) alone. Claim (3) requires a self-loop in the actual joint state. Any missing implication is represented as an explicit obligation or constructive counterexample, never as an unchecked assertion.

## Proof exclusions

The following are outside the canonical path:

- Munchausen
- Tsallis-2 distributional RL
- softmax
- transcendental/irrational arithmetic
- True Online TD
- replay buffers
- minibatch/gradient averaging
- OpenES/MR15 selection as learner exploration

## Reference repositories

CleanRL, Craftax-Baselines, Stoix, and the Efficient-CHAD repository are reference implementations/formalisations only. They may guide interface and algorithm structure but never constitute proof authority.

## Extraction contract

Agda2HS must extract the exact canonical learner module. A separate handwritten Haskell reimplementation is not an acceptable substitute. CI must compile the generated executable and compare deterministic finite witness results against Agda witness theorems.
