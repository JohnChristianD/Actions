# Theorem-first canonical learner wiki

Authority: Agda `--safe` proof terms. Haskell generation is theorem discovery/status automation only.

## Canonical monolith

The single canonical learner is:

`Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda`

Its endogenous state composes:

1. learned sparsemax attention parameters;
2. fixed-temperature sparsemax pseudo-policy with `tau = 1/8 = 16/128` in Q7 Int8 units;
3. Watkins critic as the only learned Q/policy source;
4. deterministic count-memory LCB exploration correction;
5. exact finite-rational negative q-log shaping boundary;
6. frozen unnormalised Haar transform between sparsemax attention output and recurrent input;
7. persistent signReLU GRU;
8. global F4-style optimizer with the actual coupled L2 subtraction;
9. norm-pair state (`l1`, `path`);
10. Nat clock for deterministic aperiodicity;
11. a whole-learner coercive-quadratic witness boundary.

The old duplicate monolith sources were retired after CI exposed a namespace collision between their exported `criticKernel` field names. The canonical V2 surface uses the shared Watkins-only critic and shared Dyadic GRU definitions instead of redeclaring them.

## Sparsemax policy theorem boundary

The policy temperature is fixed configuration, not learned state:

`SparsemaxTemperature = 16/128 = 1/8`.

For signed Q7 score difference `d`, the canonical two-action map is the exact clipped Q7 weight

`p_left = clip((128 + 8*d)/2, 0, 128)`

with `p_right = 128 - p_left`.

Checked finite cases include:

- equal scores: `(64,64)`;
- one-code left advantage: `(68,60)`;
- one-code right advantage: `(60,68)`.

No learned actor parameterization is introduced. The pseudo-policy is derived from the current Watkins critic/LCB score surface.

The standalone `Int8SparsemaxLiteral` module is not the promoted theorem boundary. It is used only for the shared score/pair type surface; the canonical policy semantics live in V2.

## Finite-rational negative q-log boundary

The canonical shaping value is represented by an exact numerator/denominator pair over `Agda.Builtin.Int`.

With finite reciprocal convention `recip(0) = 0`:

`qLog(0) = 1`,

and for positive integer code `n`:

`qLog(n) = (n - 1) / n`.

The negative shaping value negates the numerator. The theorem is finite and deterministic, with no floating-point or real-analysis dependency.

## LCB exploration

LCB is deterministic count-memory algebra. The canonical finite bonus table is:

`127, 63, 31, 15, 7, 3, 1, 0`

for counts `0,1,...,>=7`.

The endogenous policy pipeline is:

`Watkins Q -> LCB score correction -> fixed-temperature sparsemax -> q-log-shaped policy signal -> critic/attention/GRU/optimizer/count updates`.

No posterior or statistical-confidence interpretation is asserted.

## Learned attention versus pseudo-policy

The learned attention state is separate from the Watkins pseudo-policy boundary. Its parameters are part of the same canonical endogenous state and are advanced by `attentionStep` inside `canonicalFullStep`.

The Watkins critic remains the only learned Q/policy source. Sparsemax attention is representation/selection machinery, not a second actor optimizer.

## Haar sandwich

The frozen two-coordinate matrix is the unnormalised Haar transform

`H = [[1,1],[1,-1]]`

with

`H H^T = 2 I`.

The rows have squared norm `2` and zero cross-inner-product. It is orthogonal up to the fixed scale factor and is not orthonormal.

The canonical monolith computes the sparsemax output, applies Haar, then feeds the transformed result through the explicit recurrent-input projection before the persistent GRU step.

## GRU and Mobius representation laws

The canonical monolith imports the shared Dyadic GRU and exposes the exact persistence law:

`persistentGRUMonolith`.

It also exposes `mobiusAssociativity`, inherited from the definitional associativity of the shared `MobiusGroup` composition operator.

These are component laws inside the same generated theorem family rather than separate disconnected demonstrations.

## Global optimizer, norm pair, and coercive quadratic boundary

The actual optimizer transition contains the global L2 subtraction term. The norm-pair remains in the same monolithic state and is therefore part of the complete learner carrier.

The canonical theorem boundary is:

`FullLearnerCoerciveQuadratic K`

which contains a Nat-valued energy and strict decrease for moved states of the actual `canonicalFullStep`. This is an explicit witness boundary, not an undeclared postulate.

The reusable finite-state consequence is then the existing strict-descent exclusion of nontrivial cycles. Independently, the Nat clock gives deterministic aperiodicity of the actual canonical map.

The current formal surface does not silently turn the witness field into a theorem about all parameter choices: the Haskell generator merely checks that the proof symbols exist and that the complete Agda module typechecks under `--safe`.

## Automated theorem generation

The existing generator is:

`.ci/discovery/ExplorationTheoremGenerator.hs`

It enumerates one canonical theorem family and requires concrete proof symbols for temperature laws, finite-rational q-log, Haar orthogonality, Mobius associativity, persistent GRU, optimizer reconstruction, endogenous one-step composition, coercive decay, aperiodicity, and finite-cycle exclusion.

It then runs:

`agda --safe Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda`

CI subsequently checks the generated status source:

`Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`

Generation cannot upgrade an absent proof to `Proven`.

## CI gate

`.github/workflows/agda.yml` now:

- installs Agda 2.8.0 and stdlib 2.4;
- runs the theorem-scope guard;
- installs GHC for the Haskell generator;
- generates the canonical theorem report;
- checks shared Int8 algebra;
- checks the frozen Haar/Helmert attention-GRU boundary;
- checks the Watkins critic-only layer and regression;
- checks the V2 canonical fixed-temperature learner monolith and regression;
- checks the generated report;
- checks count-memory, signReLU semidirect, and persistent-GRU component gates.

## Theorem-status limits

The canonical surface does **not** claim:

- general neural Watkins convergence to `Q*`;
- statistical validity of the LCB table;
- posterior sampling equivalence;
- equilibrium uniqueness;
- general regret or global optimality.

Those require semantics and assumptions not present in this finite deterministic learner.

The accepted theorem class is deliberately algebraic, finite, endogenous, and kernel-checked.
