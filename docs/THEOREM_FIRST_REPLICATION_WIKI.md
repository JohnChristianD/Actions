# Theorem-first canonical learner wiki

Authority: Agda `--safe` proof terms. Haskell generation and auditing are automation only.

## Canonical monolith

The single canonical learner is:

`Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda`

Its endogenous state composes:

1. a learned sparsemax attention/representation component;
2. a fixed-temperature sparsemax action-selection map with `tau = 1/8 = 16/128` in Q7 Int8 units;
3. Watkins critic as the only learned Q/action-selection source;
4. deterministic count-memory LCB exploration correction;
5. exact finite-rational negative q-log state and an endogenous signed shaping control;
6. an exactly dyadically normalized 4-dimensional Walsh-Hadamard boundary;
7. a finite-rational Mobius recurrent carrier using `x / (1 - x)` away from its singular input boundary;
8. persistent recurrent parameter coordinates;
9. global F4-style optimizer with the coupled L2 subtraction;
10. norm-pair state (`l1`, `path`);
11. Nat clock for deterministic aperiodicity;
12. a whole-learner coercive-quadratic witness boundary.

## Learned sparsemax attention is not an actor

This distinction is theorem-level, not terminology:

`learnedSparsemaxAttentionWeights` belongs to the learned representation state;

`canonicalPolicy` is computed only from Watkins critic scores plus deterministic LCB/count scheduling.

The canonical carrier has no independently optimized actor parameter block. The theorem

`canonicalPolicy-attention-invariant`

states that replacing the learned attention state leaves `canonicalPolicy` unchanged. Thus learned sparsemax attention cannot secretly become a second actor through the policy definition.

The learner does update the attention representation through `attentionStep`, but action selection does not consume that learned attention state. The current recurrent path likewise receives the canonical action-selection transform, not learned attention weights. This is an explicit architectural boundary, not an accidental omission.

## Fixed-temperature sparsemax

The temperature is fixed configuration:

`16/128 = 1/8`.

For signed Q7 score difference `d`:

`p_left = clip((128 + 8*d)/2, 0, 128)`

and

`p_right = 128 - p_left`.

Checked finite cases are `(64,64)`, `(68,60)`, and `(60,68)` for tie, unit-left, and unit-right differences.

The duplicate standalone sparsemax literal surface is retired. The canonical policy algebra is owned by V2 and the actor-free Watkins layer.

## Finite-rational Mobius recurrent carrier

The recurrent hidden coordinate is represented over an exact numerator/denominator carrier.

The active boundary is the Mobius ratio

`x / (1 - x)`

with a total finite boundary at the singular input `x = 1`.

`mobiusRatio8-law` proves the exact rational form away from the singular point, while `mobiusSingularity` records the explicit totalization at that point.

The recurrent parameter coordinates are independent of the previous hidden state and persist under `gruStep`; the recurrence remains input-dependent because its hidden output is defined from the current input through `mobiusRatio8`.

`persistent-preservation` and `canonicalPersistentGRUPreservation` expose the component and whole-canonical persistence laws.

## Identity and pessimistic initialization

Identity initialization is explicit for the recurrent parameter block.

The signed Q7 semantic carrier has values `-128 ... 127`, so raw Int8 code `128` denotes the least semantic Q7 value. The critic therefore uses:

`maxPessimisticCritic = criticState (int8OfNat 128) (int8OfNat 128)`.

The formal surface distinguishes this initialization theorem from cycle exclusion. Pessimistic initialization alone does not imply that every later update is descending.

## Walsh-Hadamard boundary

The old unnormalised two-coordinate transform has been retired from the canonical path.

The active transform uses the dimension-four Walsh-Hadamard basis `H₄ / 2`. The raw basis satisfies

`H₄ H₄ᵀ = 4 I`,

so the fixed factor `1/2` gives the exact orthonormal basis. Dimension four is `4^1`, keeping normalization dyadic and exact.

`walshOrthonormal` records all diagonal norm and off-diagonal orthogonality equalities for the base basis. The canonical learner lifts the two action coordinates into the 4-dimensional representation before applying the transform.

The transform is a linear map, not an associative algebra operation. Associativity remains the separate theorem of the Mobius composition operator.

## Negative q-log shaping

The q-log value remains an exact finite numerator/denominator pair, while the signed scale used by the learner is now an endogenous state function of the current canonical policy surface:

`endogenousNegativeScale8`

and

`canonicalQLogControlStep`.

The full one-step map exposes `canonicalFullStep-qLogControl`, so the shaping scale is not merely a fixed unused constant.

This remains a finite deterministic algebraic shaping variant. No Bayesian posterior interpretation or continuous-real identity is asserted by naming alone.

## LCB action-selection pipeline

The canonical path is:

`Watkins Q -> deterministic LCB/count correction -> fixed-temperature sparsemax -> endogenous q-log learner signal -> Walsh-Hadamard recurrent input -> finite Mobius GRU update -> optimizer/count/q-log updates`.

LCB uses the finite table

`127, 63, 31, 15, 7, 3, 1, 0`

for counts `0,1,...,>=7`.

No statistical-confidence or posterior-sampling theorem is claimed.

## Mobius composition and semidirect boundary

`mobiusAssociativity` and `mobiusAssociativityWindow` are exact consequences of the definitional associativity of `composeAction`.

`persistentGRUMonolith`, `canonicalPersistentGRUPreservation`, and the Mobius recurrent input laws place persistence and associativity in the same theorem family.

The finite-cycle theorem remains conditional on an actual `LyapunovCertificate` or equivalent discharged monotone invariant for the concrete update. Mobius associativity and pessimistic initialization alone do not establish a global no-cycle theorem.

## Strongest theorem gains currently available

The strongest unconditional algebraic gains introduced by this refactor are:

- attention/policy separation by the exact `canonicalPolicy-attention-invariant` theorem;
- exact finite-rational Mobius ratio boundary with an explicit singularity theorem;
- state-independent recurrent parameter persistence with explicit input-driven hidden output;
- exact dyadic Walsh-Hadamard orthogonality at dimension `4 = 4^1`;
- endogenous q-log control and its one-step composition law;
- maximal signed-Q7 pessimistic critic initialization.

A stronger whole-learner finite-cycle exclusion remains a conditional theorem until a concrete strict-decrease measure for the new update is discharged. The existing `FullLearnerCoerciveQuadratic` witness is still the formal boundary for that result.

## Tsallis-2 / entmax

SciSpace literature identifies sparsemax as the `alpha = 2` member of the alpha-entmax family and connects the corresponding regularization to Tsallis statistics and Fenchel-Young formulations.

That gives a potentially useful *new theorem boundary* if formalized: a finite variational or entropy-optimality characterization of the exact sparsemax map. It does not automatically imply stronger Mobius associativity, Walsh orthonormality, or finite-cycle exclusion. Therefore the computational kernel remains sparsemax until the additional variational theorem is actually discharged in Agda.

## Automation and pruning

The canonical theorem generator is:

`.ci/discovery/ExplorationTheoremGenerator.hs`

The consolidated redundancy audit is:

`.ci/discovery/PruneRedundantComponents.hs`

The audit covers q-log, action selection, learned attention, Walsh-Hadamard, recurrent nonlinearities, GRU persistence, optimizer, whole-step definitions, and retired duplicate component paths. It does not ban or delete the q-log algorithm family by naming it.

The repository's active automation is Agda/Haskell/declarative-environment oriented. The retired Python theorem guard is no longer part of the gate.

The generated theorem report remains accepted only when the named terms exist and the corresponding modules pass `agda --safe`.

## Theorem-status limits

The canonical surface does **not** claim:

- general neural Watkins convergence to `Q*`;
- statistical validity of the LCB table;
- posterior sampling equivalence;
- equilibrium uniqueness;
- general regret or global optimality;
- that learned sparsemax attention is an independent actor;
- that learned attention currently drives the recurrent path;
- that Walsh-Hadamard multiplication itself is associative;
- that initialization alone proves absence of cycles;
- that the endogenous q-log scale automatically gives a global Lyapunov function.

The accepted theorem class is finite, algebraic, endogenous, and kernel-checked.
