# Canonical Coupled Semantics

## 1. Signed Int8 carrier

`CanonicalCoupledF4Learner.agda` defines `Signed8` with `pos8 n` and `neg8 n`.

For an imported `L.Int8` code, `fromInt8` interprets codes 0..127 as nonnegative and codes 128..255 as negative values represented by `neg8 (255 - code)`.

`signedClip` maps a signed value back to the Int8 code range with saturation at +127 and -128.

Canonical F4 arithmetic is therefore signed/clipped, not the raw modular arithmetic used by the older general learner helpers.

## 2. Canonical F4 state and parameters

State: `(qTheta, rTheta, qE, rE, rL, ell)`.

Here `qTheta`, `rTheta`, `qE`, `rE`, and `rL` are `L.Int8`, while `ell` is `Signed8`.

Shared parameters: `(beta₂, betaTheta)`.

There is no canonical `l2Global` state field.

## 3. Error and level updates

Define:

θfull = qTheta +f4 rTheta

efull = qE +f4 rE

enew = scaledMulF4 beta₂ efull +f4 scaledMulF4 (1 -f4 beta₂) g

rL′ = rL +f4 enew

ell′ = ell + sign(rL′), where the sign contribution is represented in the signed residual carrier,

rL″ = rL′ -f4 sgnF4(rL′).

## 4. Canonical hardsign and parameter-level L2

`canonicalSign = L.hardSignGate`.

The gate is exactly sign(x): negative inputs map to Int8 code 255, zero maps to code 0, and positive inputs map to code 1.

The step uses the old level `ell s` when computing the scale `pow2Ell8 (ell s)`.

The global parameter-level term is:

Δθ = scaledMulF4 (pow2Ell8 (ell s)) (canonicalSign g) -f4 scaledMulF4 (betaTheta p) (thetaFull s).

Then:

qTheta′ = θfull +f4 Δθ

rTheta′ = θfull -f4 qTheta′

qE′ = enew

rE′ = efull -f4 enew.

This is the coupled global term requested by the canonical learner. It is not per-coordinate optimizer state and it is not a decoupled L2 update.

## 5. Scaled multiplication

`scaledMulF4 x y` multiplies signed carriers and divides the signed product by 128 before clipping.

A kernel-checked example is `64 * 64 / 128 = 32` in the canonical representation.

A clipping example is `127 + 1 = 127` under canonical signed clipping.

## 6. Coupled learner composition

`canonicalCoupledStep` performs one coupled step in this order:

1. derive the policy action from sparsemax and count state;
2. form the Munchausen-shaped input;
3. increment the global clock;
4. update the selected Q entry and action count;
5. apply the state-independent sign-gated GRU transition to the shaped input;
6. apply canonical six-state F4 to the same shaped input;
7. advance the norm pair.

The canonical state contains clock, Q-vector, count-vector, last action, GRU state, canonical F4 state, and norm pair.

## 7. Legacy general learner semantics

`GeneralFullCoupledLearnerMonolith.agda` remains a distinct legacy kernel.

Its `Int8` helpers are raw modular code arithmetic.

Its GRU uses `hardSignGate` but applies the modular `int8Add`, `int8Mul`, and `int8Neg` operations.

Its old F4 state has five Int8 fields `(thetaQ, residualQ, errorQ, errorResidual, l2Global)`, and `f4Step` quantizes a raw value by multiples of 16 while preserving `l2Global` unchanged.

That old F4 is useful as a generic theorem substrate but is not the canonical six-state F4 semantics.

## 8. Rational branch machinery

The theorem monolith defines `finitePiecewiseRational` using three sign branches: negative -> 255/1, zero -> 0/1, positive -> `mobiusRatio`.

This is theorem-side symbolic representation machinery. It is not the canonical GRU gate and should not be documented as a rational replacement for `sign(x)`.