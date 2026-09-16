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

This initialization theorem is deliberately separate from cycle exclusion. Pessimistic initialization alone does not imply that every later update is descending.

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

The existing strict-descent finite-cycle exclusion theorem remains structurally preserved: `noNontrivialFiniteCycle` still derives the contradiction from a `LyapunovCertificate`. What is **not** yet proved is a new unconditional certificate specifically from the Mobius replacement or pessimistic initialization.

## Ring algebra: deliberately not required

The present algebra needs a monoid of endomorphisms under composition, not a ring. Adding additive inverses, distributivity, and a ring carrier would be mathematically interesting only if the learner needs those operations in an actual theorem.

For the ratio `x / (1 - x)`, an ordered field or exact rational carrier is more natural than forcing the recurrence into a ring abstraction. The singular boundary also means that an unrestricted ring statement would be the wrong abstraction unless a domain predicate is carried explicitly.

Therefore the current theorem surface keeps:

`MobiusAction + composeAction + identityAction + associativity`

rather than inventing ring structure for its own sake.

## Min-max, Jensen, regret, Pareto, and Nash boundary

These concepts are related but not interchangeable.

A Jensen inequality can provide a convexity/concavity bound or a variational sandwich. A saddle point is a stronger structural condition for a two-player objective, and in a zero-sum setting the saddle condition is the local algebraic core behind minimax equality when the required convexity/compactness or finite-game assumptions hold.

A Nash equilibrium is the no-unilateral-deviation condition for a general game. In a two-player zero-sum game, saddle points and Nash equilibria coincide at equilibrium values, but a general Nash equilibrium is not synonymous with a saddle condition.

Regret bounds are performance statements over play sequences, not themselves saddle certificates. Pareto efficiency concerns multi-objective dominance and likewise is not a synonym for zero-sum minimax optimality.

Nothing in the present deterministic learner automatically supplies a convex-concave payoff, two-player game, Jensen sandwich, regret process, or Pareto order. Adding those labels without a newly defined game functional would weaken theorem hygiene rather than strengthen the composition theorem.

## Variational Tsallis-2 / entmax question

Sparsemax is the alpha=2 member of the alpha-entmax family, and the literature gives variational/Fenchel-Young/Tsallis characterizations. Those are genuinely new mathematical statements relative to the current exact finite code map when formalized.

However, the variational theorem is worth adding only if it proves something that the existing sparsemax algebra cannot already prove. A useful non-trading upgrade would be an Agda theorem of the form:

1. the canonical finite sparsemax map is the unique optimizer of a precisely stated finite quadratic/Tsallis-2 objective;
2. the optimizer satisfies an exact simplex/projection characterization;
3. that variational certificate composes with the actual Watkins/LCB policy state without replacing the existing action-selection or cycle theorems.

That would add a new theorem rather than trade away an existing one. It would not by itself prove Mobius associativity, Walsh orthonormality, regret, Pareto efficiency, Nash equilibrium, or finite-cycle exclusion.

## Hard-sign + F4/L2 theorem boundary

Hard-sign changes the activation algebra. The global optimizer still contains the explicit coupled L2 subtraction.

A genuinely new theorem would require a discharged statement such as monotone energy decrease, parameter reconstruction, or a finite invariant for the **new** hard-sign update. The existing `f4ParameterInvariant` proves exact reconstruction of the F4 update, but it is not itself a convergence theorem.

The strongest non-trading target is therefore a theorem connecting the hard-sign recurrent update and the F4/L2 state transition to one explicitly defined finite energy. Once that certificate is proved, the existing finite-cycle exclusion theorem can consume it without sacrificing the older component identities.

## Strongest theorem gains currently available

The strongest unconditional algebraic gains introduced by this refactor are:

- attention/policy separation by the exact `canonicalPolicy-attention-invariant` theorem;
- exact finite-rational Mobius ratio boundary with an explicit singularity theorem;
- state-independent recurrent parameter persistence with explicit input-driven hidden output;
- exact dyadic Walsh-Hadamard orthogonality at dimension `4 = 4^1`;
- endogenous q-log control and its one-step composition law;
- maximal signed-Q7 pessimistic critic initialization.

The existing strict-descent finite-cycle theorem remains available through a concrete `LyapunovCertificate`, but a new unconditional global certificate still needs to be proved for the refactored update.

## Automation and pruning

The canonical theorem generator is:

`.ci/discovery/ExplorationTheoremGenerator.hs`

The consolidated redundancy audit is:

`.ci/discovery/PruneRedundantComponents.hs`

The audit covers q-log, action selection, learned attention, Walsh-Hadamard, recurrent nonlinearities, GRU persistence, optimizer, whole-step definitions, and retired duplicate component paths. It does not ban or delete the q-log algorithm family by naming it.

The repository's active automation is Agda/Haskell/declarative-environment oriented. The retired Python theorem guard is no longer part of the gate.

The generated theorem report remains accepted only when the named terms exist and the corresponding modules pass `agda --safe`.

## What to do next after the refactor is complete

1. Run the complete `agda --safe` gate and treat any failure as a semantic/type-level defect, not as a documentation problem.
2. Discharge the new hard-sign/F4/L2 whole-learner energy certificate, if one exists without assuming extra structure. Feed it into the existing `noNontrivialFiniteCycle` theorem.
3. Prove the exact finite variational characterization of the fixed-temperature sparsemax map if it adds a new optimizer/projection theorem without replacing an existing identity.
4. Strengthen the Walsh-Hadamard result from the base four-dimensional Gram identities to the actual active recurrent-input carrier and norm preservation.
5. Replace any remaining stale component names in tests/gates only after their replacement theorem compiles.
6. Re-run the consolidated Haskell redundancy audit and delete only sources it identifies as genuinely unreachable or superseded.
7. Keep the merge history atomic: after the final green theorem gate, a squash merge is the cleanest PR automation path for this branch because the branch contains many repair/refactor commits.
8. Only then close/remove obsolete exploration branches and mark the canonical PR ready for review. Do not delete a branch merely because its name is old; first verify that its commit is fully subsumed by the canonical head.

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
- that the endogenous q-log scale automatically gives a global Lyapunov function;
- that a Jensen inequality alone establishes minimax, regret, Pareto efficiency, or Nash equilibrium.

The accepted theorem class is finite, algebraic, endogenous, and kernel-checked.
