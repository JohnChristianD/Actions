# Verification Status

## Current Safe Agda closure

Workflow: `.github/workflows/coupled-f4-closure.yml`.

Latest run: `35287074544`.

Head checked: `09e263b77bb92a3a0d6123382edee895bc73b179`.

Toolchain: Agda 2.8.0 with Agda standard library 2.4, all checks invoked with `--safe`.

## Passed in the latest run

1. `F4HardsignKernel.agda` passed.
2. `CanonicalCoupledF4Learner.agda` passed.
3. `CanonicalCoupledCompositionTheorems.agda` passed.

These three are therefore the current kernel-checked semantic closure surface.

## Current blocker

`GeneralFullCoupledTheoremsMonolith.agda` is still failing.

The latest exact diagnostic is at line 592: `payoff` is not in scope in the defining equation of `finiteSionSandwich`.

The error is a binder-scope issue, not evidence that the canonical F4 or coupled-composition semantics are wrong.

The downstream jobs `GeneralReservoirAttractorTheorems.agda` and `MonolithCompositeReservoirTheorem.agda` are skipped in that workflow whenever the generalized theorem monolith fails.

## Interpretation rule

A theorem is marked verified here only when the target Agda module passes the Safe Agda workflow.

A record field such as `LyapunovCertificate.strictDecrease`, `AttractorRecallCertificate.basinHit`, `ReservoirConditionCertificate.inverseLaw`, or `KKTPathCertificate.kktProof` is documented as a supplied certificate requirement, not as an automatically derived property of the learner.

## Current closure picture

The canonical semantic kernel and the simultaneous reservoir/depth/associativity package are green.

The generalized theorem layer remains one scope repair away from exposing the next actual theorem-module errors. Once that gate is green, the reservoir-attractor and composite theorem modules must be re-run independently before they can be called closed.
