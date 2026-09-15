# Theorem-first canonical learner wiki

Authority: Agda `--safe` proof terms. Haskell generation is only theorem discovery/status automation.

## Canonical monolith

The current canonical learner is:

`Exotic/ERL/FullCoupled/CanonicalSparsemaxLearner.agda`

Its single endogenous state composes:

1. learned sparsemax attention parameters;
2. fixed-temperature sparsemax pseudo-policy with `tau = 1/8 = 16/128` in Q7 Int8 units;
3. Watkins critic as the only learned Q/policy source;
4. deterministic count-memory LCB exploration correction;
5. exact finite-rational negative q-log shaping boundary;
6. frozen unnormalised Haar transform between sparsemax attention output and recurrent input;
7. persistent signReLU GRU;
8. global F4-Int-U(p) optimizer with the actual coupled L2 term;
9. norm-pair state (`l1`, `path`);
10. Nat clock for deterministic aperiodicity;
11. an explicit whole-learner coercive-quadratic witness boundary.

The previous `SparsemaxWatkinsMonolith.agda` remains the lower-level core used by the canonical wrapper. The wrapper replaces its policy boundary with exact fixed-temperature Q7 sparsemax while retaining the Watkins-only critic and the shared endogenous signal flow.

## Sparsemax policy theorem boundary

The policy temperature is not learned and is not stored as actor state:

`SparsemaxTemperature = 16/128 = 1/8`.

For the signed Q7 score difference `d`, the two-action map is implemented exactly as the clipped Q7 weight

`p_left = clip((128 + 8*d)/2, 0, 128)`

with `p_right = 128 - p_left`.

This produces exact finite cases such as:

- equal scores: `(64,64)`;
- one-code left advantage: `(68,60)`;
- one-code right advantage: `(60,68)`.

No separate learned actor parameterization is present.

## Finite-rational negative q-log boundary

The canonical finite-rational layer uses an exact numerator/denominator representation over `Agda.Builtin.Int`.

With the finite reciprocal convention `recip(0) = 0`:

`qLog(0) = 1`,

and for positive integer code `n`:

`qLog(n) = (n - 1) / n`.

The negative shaping value is exactly `-qLog(n)`. This is represented without floating point and without real-analysis infrastructure.

## LCB exploration

LCB is deterministic count-memory algebra. The canonical finite bonus table remains:

`127, 63, 31, 15, 7, 3, 1, 0`

for counts `0,1,...,>=7`.

The policy pipeline is:

`Watkins Q -> LCB score correction -> fixed-temperature sparsemax -> policy signal -> critic/GRU/optimizer/count updates`.

No posterior or statistical-confidence interpretation is asserted.

## Learned attention versus pseudo-policy

The learned attention state is separate from the Watkins pseudo-policy boundary. Its parameters are part of the same canonical endogenous state and are updated by an explicit attention-step kernel.

The Watkins critic remains the only learned Q/policy source. Sparsemax attention is representation/selection machinery, not a second policy optimizer.

## Haar sandwich

The frozen two-coordinate matrix is the unnormalised Haar transform

`H = [[1,1],[1,-1]]`

with

`H H^T = 2 I`.

The rows have squared norm `2` and zero cross-inner-product. It is orthogonal up to the fixed scale factor and is not orthonormal.

The canonical monolith explicitly computes the sparsemax output, applies Haar, then feeds an explicit recurrent-input projection into the persistent GRU. No transform parameters are learned.

## Global optimizer and coercive quadratic boundary

The actual optimizer step is inherited from the F4-Int-U(p) core and includes the global L2 subtraction in the parameter update. The norm pair remains in the same learner state.

The canonical theorem boundary is:

`FullLearnerCoerciveQuadratic K`

which provides a Nat-valued energy and a strict decrease theorem for moved states of the actual `canonicalFullStep`. This witness is a theorem input, not an undeclared postulate.

The direct consequence is the reusable finite-state result that a strict Lyapunov descent certificate excludes nontrivial finite cycles. Independently, the Nat clock gives deterministic aperiodicity for the actual canonical map.

## Automated theorem generation

The existing generator remains authoritative for discovery/status:

`.ci/discovery/ExplorationTheoremGenerator.hs`

It now enumerates only the canonical learner theorem family and checks concrete proof symbols before invoking:

`agda --safe Exotic/ERL/FullCoupled/CanonicalSparsemaxLearner.agda`

CI then checks the generated report:

`Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`

The generator cannot promote a missing proof into a theorem. A theorem family is accepted only when the required proof symbols exist and the actual Agda module exits successfully under `--safe`.

## CI gate

`.github/workflows/agda.yml` now:

- installs Agda 2.8.0 and stdlib 2.4;
- runs the permanent theorem-scope guard;
- installs GHC for the existing Haskell generator;
- runs the generator;
- checks shared Int8 algebra;
- checks the canonical fixed-temperature learner monolith and regression;
- checks the generated theorem report;
- checks the retained Watkins, count-memory, signReLU semidirect, and persistent-GRU component gates.

## Theorem-status limits

The canonical surface does **not** claim:

- general neural Watkins convergence to `Q*`;
- statistical validity of the LCB table;
- posterior sampling equivalence;
- equilibrium uniqueness;
- general regret or optimality.

Those would require additional semantics and assumptions not present in the finite deterministic learner.

The accepted theorem class is therefore deliberately algebraic, finite, endogenous, and kernel-checked.
