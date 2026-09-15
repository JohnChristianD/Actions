# Theorem-first canonical learner wiki

Authority: Agda `--safe` proof terms. Haskell generation is theorem discovery/status automation only.

## Canonical monolith

The single canonical learner is:

`Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda`

Its endogenous state composes:

1. a learned sparsemax attention/representation component;
2. a fixed-temperature sparsemax action-selection map with `tau = 1/8 = 16/128` in Q7 Int8 units;
3. Watkins critic as the only learned Q/policy source;
4. deterministic count-memory LCB exploration correction;
5. exact finite-rational negative q-log shaping boundary;
6. frozen unnormalised Haar transform;
7. persistent signReLU GRU;
8. global F4-style optimizer with the actual coupled L2 subtraction;
9. norm-pair state (`l1`, `path`);
10. Nat clock for deterministic aperiodicity;
11. a whole-learner coercive-quadratic witness boundary.

The old duplicate monolith sources were retired after CI exposed a namespace collision between their exported `criticKernel` field names. The canonical V2 surface uses the shared Watkins-only critic and shared Dyadic GRU definitions instead of redeclaring them.

## Sparsemax action-selection theorem boundary

The fixed sparsemax temperature is configuration, not learned policy state:

`SparsemaxTemperature = 16/128 = 1/8`.

For signed Q7 score difference `d`, the canonical two-action map is the exact clipped Q7 weight

`p_left = clip((128 + 8*d)/2, 0, 128)`

with `p_right = 128 - p_left`.

Checked finite cases include:

- equal scores: `(64,64)`;
- one-code left advantage: `(68,60)`;
- one-code right advantage: `(60,68)`.

No independently optimized actor exists in the canonical carrier. The action-selection pair is computed from the Watkins critic and deterministic LCB/count surface.

The separate learned sparsemax attention component is not this action-selection policy. It is representation/attention state, analogous in role to a Transformer attention component, and it must not be described as a second actor.

The standalone `Int8SparsemaxLiteral` module is not the promoted theorem boundary. The canonical policy semantics live in V2.

## Finite-rational negative q-log boundary

The canonical shaping value is represented by an exact numerator/denominator pair over `Agda.Builtin.Int`.

With finite reciprocal convention `recip(0) = 0`:

`qLog(0) = 1`,

and for positive integer code `n`:

`qLog(n) = (n - 1) / n`.

The negative shaping value negates the numerator. The theorem is finite and deterministic, with no floating-point or real-analysis dependency.

The current implementation also exposes a signed q-log shaping control used by the learner signal. This is a finite algebraic q-log variant. It should not be advertised as a full real-valued derivation or as a Bayesian/posterior construction.

## LCB exploration

LCB is deterministic count-memory algebra. The canonical finite bonus table is:

`127, 63, 31, 15, 7, 3, 1, 0`

for counts `0,1,...,>=7`.

The action-selection path is:

`Watkins Q -> LCB score correction -> fixed-temperature sparsemax -> deterministic learner signal -> critic/attention/GRU/optimizer/count updates`.

No posterior or statistical-confidence interpretation is asserted.

## Learned attention versus action selection

The learned attention state is separate from the Watkins action-selection boundary. Its parameters are part of the same endogenous state and are advanced by `attentionStep` inside `canonicalFullStep`.

The key semantic separation is:

`learnedSparsemaxAttentionWeights` = learned representation/attention coordinates;

`canonicalPolicy` = Watkins/LCB-derived action-selection coordinates.

There is no separate actor optimizer and no second policy learner hidden inside sparsemax attention.

Current V2 detail: the learned attention state is updated inside the monolith, but the present `canonicalGRUStep` feeds Haar with `canonicalPolicy`, not with `learnedSparsemaxAttentionWeights`. Therefore the current source should **not** be documented as an already-connected learned-attention-to-GRU path. That connection is a distinct future composition change, not a theorem that the current code already proves.

## Haar transform

The frozen two-coordinate matrix used in the present recurrent path is the unnormalised Haar transform

`H = [[1,1],[1,-1]]`

with

`H H^T = 2 I`.

The rows have squared norm `2` and zero cross-inner-product. It is orthogonal up to the fixed scale factor and is not orthonormal.

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

The current formal surface does **not** turn the witness field into a theorem about all parameter choices: the Haskell generator merely checks that the proof symbols exist and that the complete Agda module typechecks under `--safe`.

## Tsallis-2 / entmax note

For the relevant attention/action map, merely renaming sparsemax as Tsallis-2 entmax does not buy a stronger theorem. The useful upgrade would be a new proved variational or entropy-optimality characterization of the exact finite map. Without that additional theorem, the algebraic kernel and composition laws are unchanged, so the canonical surface remains sparsemax.

SciSpace literature places sparsemax within the sparse/alpha-entmax attention family and discusses the alpha = 2 connection to Tsallis statistics. The stronger formal claim would therefore have to be proved in Agda rather than imported by terminology.

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
- audits the active q-log shaping boundary and duplicate q-log implementations;
- installs GHC for the Haskell generator;
- generates the canonical theorem report;
- checks shared Int8 algebra;
- checks the frozen Haar/Helmert boundary;
- checks the Watkins critic-only layer and regression;
- checks the V2 canonical fixed-temperature learner and regression;
- checks the generated report;
- checks count-memory, signReLU semidirect, and persistent-GRU component gates.

## Theorem-status limits

The canonical surface does **not** claim:

- general neural Watkins convergence to `Q*`;
- statistical validity of the LCB table;
- posterior sampling equivalence;
- equilibrium uniqueness;
- general regret or global optimality;
- that learned sparsemax attention is an independent actor;
- that the current GRU is already connected to the learned attention weights.

Those require semantics and assumptions not present in this finite deterministic learner.

The accepted theorem class is deliberately algebraic, finite, endogenous, and kernel-checked.