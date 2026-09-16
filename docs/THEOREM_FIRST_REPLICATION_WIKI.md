# Theorem-first canonical learner wiki

Authority: Agda `--safe` proof terms. Haskell discovery and redundancy auditing are automation only.

## Canonical source

The learner monolith is:

`Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

It has no project-local Agda imports. Its learner state is endogenous. No environment type, reward process, observation kernel, transition-probability space, random-variable model, posterior sampler, replay buffer, or statistical limit is included.

The environment remains external. An application can instantiate the finite learner kernel, while the canonical theorem source contains no separable environment model.

## Learner architecture

The monolith contains, in one state transition:

1. Watkins critic state as the sole learned Q/action-selection source;
2. deterministic count-memory LCB correction;
3. fixed-temperature sparsemax with Int8 dyadic temperature code `16`, representing `1/8` on the Q7 scale;
4. negative finite-rational q-log / Munchausen-style shaping;
5. learned sparsemax attention as representation state, not an independently optimized actor;
6. a four-dimensional Walsh-Hadamard representation boundary;
7. a custom recurrent GRU carrier with a state-independent hard-sign-derived gate;
8. finite-rational Mobius activation `x / (1 - x)` with an explicit singular boundary;
9. persistent recurrent parameter, noise, optimizer-token, and L2-token coordinates;
10. global F4-Int-U-style optimizer state with explicit global L2 correction;
11. `NormPair` state carrying `l1` and `path` components;
12. deterministic Nat clock and complete `canonicalFullStep` composition.

All of these are learner-internal definitions.

## Watkins + sparsemax + LCB

`canonicalPolicy` consumes Watkins critic values and LCB count state, then applies fixed-temperature sparsemax.

The temperature is fixed:

`16 / 128 = 1 / 8`.

Checked finite laws:

`(0,0) -> (64,64)`

`(1,0) -> (68,60)`

`(0,1) -> (60,68)`

The count-memory schedule is the finite table:

`127, 63, 31, 15, 7, 3, 1, 0`.

No statistical-confidence interpretation is asserted by the finite algebra alone.

## Negative q-log / Munchausen-style boundary

`finiteQLog8` stores a finite numerator/denominator pair.

`negativeFiniteQLog8` negates the numerator exactly in that finite carrier.

`negativeFiniteQLogLaw` is definitional.

`canonicalQLogControlStep` derives its signed coefficient from the current policy, and `canonicalQLogStep` stores the corresponding finite q-log value inside the complete state.

No continuous-real identity, Bayesian interpretation, or statistical optimality claim is attached to the name.

## Learned attention is not an actor

`LearnedSparsemaxAttention` is representation state.

`canonicalPolicy-attention-invariant` proves that replacing attention state leaves action selection unchanged.

At the same time, `canonicalGRUStep` consumes the learned attention representation through the Walsh boundary. Thus attention is genuinely part of the learner computation while remaining separate from the Watkins policy source.

## Custom GRU boundary

`GRUState` contains hidden state, three recurrent matrices, three noise coordinates, and global optimizer/L2 control coordinates.

`gateFromInput` depends only on the current Int8 input. The finite hard-sign branch is:

`negative | zeroSign | positive`

with gate codes `0`, `64`, and `128`.

`gruStep` uses that gate and the finite Mobius activation while preserving the persistent coordinates by construction.

`persistent-preservation`, `gruParameterPersistence`, and `gruActivationBoundary` are unconditional equalities.

This is a custom finite GRU-style recurrence, not an assertion of identity with every textbook GRU.

## Mobius algebra

`mobiusRatio8-law` proves the exact finite rational form away from the singular input.

`mobiusSingularity` records the explicit total finite boundary at signed input `1`.

`MobiusAction` and `composeAction` form an ordinary composition carrier, with `mobiusAssociativity` proved definitionally.

This does not imply associativity of sparsemax, Walsh transformation, or the whole learner transition.

## Walsh-Hadamard boundary

The dimension-four basis satisfies the exact Gram equalities:

`H4 H4^T = 4 I`.

`walshOrthonormal` packages the diagonal and off-diagonal equalities, while the active representation boundary uses the dyadic factor-of-two representation carrier.

The learner lifts attention coordinates into four dimensions before applying the Walsh map.

## Global optimizer and NormPair

`F4IntUState` is the optimizer state.

`F4IntUKernel.globalL2` is consumed directly by `f4ThetaStep` through the exact finite correction `l2Correction`.

`f4ParameterInvariant` is an unconditional constructor equality for the resulting quantized theta coordinate. It is an algebraic reconstruction theorem, not a convergence theorem.

`NormPair` is stored in the full learner state and is preserved by `canonicalFullStep`.

## Complete learner transition

`canonicalFullStep` updates, in one deterministic endogenous map:

`clock, Watkins, attention, GRU, optimizer, LCB counts, q-log control, q-log value`

while retaining `NormPair`.

The projection equalities are:

`canonicalFullStep-clock`

`canonicalFullStep-watkins`

`canonicalFullStep-attention`

`canonicalFullStep-gru`

`canonicalFullStep-optimizer`

`canonicalFullStep-counts`

`canonicalFullStep-qLog`

`canonicalFullStep-qLogControl`

`canonicalRecurrentInput-law` exposes the exact attention -> Walsh -> GRU composition.

`canonicalPersistentGRUPreservation` deduces persistent-coordinate preservation on that actual composed path.

## Unconditional contradiction and negation theorems

The canonical learner does not need a coercive or Lyapunov certificate premise for its cycle exclusions.

The complete state carries a Nat `clock`, and every `canonicalFullStep` applies `suc` to that clock. Therefore:

`canonicalStep-not-fixed`

proves every one-step transition is non-fixed.

`clockAfter` proves exact clock accumulation:

`clock (iterateCanonical K n s) = clock s + n`.

From that, `canonicalAperiodic` proves:

`iterateCanonical K (suc n) s != s`.

`canonicalOrbitNonFixed` deduces non-fixedness at every orbit point.

`canonicalNoNontrivialFiniteCycle` turns a hypothetical finite return directly into `⊥` by contradiction through the clock equation.

No Lyapunov witness, environment condition, stochastic assumption, or convergence hypothesis is supplied.

## Count-memory contradiction

`canonicalTotalCountStep` proves that every complete learner step increases `totalCount` by one.

`canonicalNoCountedTwoCycle` derives a contradiction from a hypothetical two-cycle by applying `totalCount` to the cycle equality and obtaining `suc (suc n) = n`, discharged by `suc-suc-not-self`.

This is a deterministic count-memory theorem, not a statistical claim about LCB confidence.

## What is and is not proved

Proved unconditionally by the source definitions and the generated regression surface, subject to the fresh `agda --safe` gate:

- environment-agnostic learner state;
- Watkins-only action-selection source;
- fixed-temperature sparsemax regression laws;
- finite negative q-log constructor law;
- learned-attention/policy separation;
- hard-sign input-only gate law;
- Mobius rational boundary and associativity;
- Walsh Gram/orthogonality laws;
- GRU persistence;
- actual attention -> Walsh -> GRU composition law;
- F4 theta reconstruction law;
- complete-step projection laws;
- one-step non-fixedness;
- arbitrary-period no-return theorem from clock contradiction;
- orbit non-fixedness;
- count-memory two-cycle exclusion.

Not claimed merely from those facts:

- Watkins convergence to `Q*` for arbitrary environments;
- almost-sure or expected convergence;
- LCB calibration or confidence correctness;
- posterior sampling equivalence;
- regret or global optimality;
- Nash equilibrium, Pareto efficiency, or minimax equality;
- Mamba, SSRN, Transformer, or generic-RNN equivalence;
- a global Nat-valued strict Lyapunov decrease theorem for this clocked transition.

## Redundancy pruning

The automatic audit is:

`.ci/discovery/PruneRedundantLearnerModules.hs`

Default mode is dry-run. `--apply` deletes only candidates whose module name has zero repository-local import users.

## Generated proof status

`.ci/discovery/ExplorationTheoremGenerator.hs` checks the required theorem symbols in the single monolith, runs `agda --safe`, and writes:

`Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`

Haskell only reports status. Agda proof terms remain authoritative.
