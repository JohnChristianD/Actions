# Theorem-first canonical learner wiki

Authority: Agda `--safe` proof terms. Haskell discovery and redundancy auditing are automation only.

## Canonical source

The learner monolith is:

`Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

It has no project-local Agda imports. Its learner state is endogenous. No environment type, reward process, observation kernel, transition-probability space, random-variable model, posterior sampler, replay buffer, or statistical limit is included.

The environment remains an external concern: an application may feed finite learner inputs into the learner's `FullLearnerKernel`, but the canonical theorem source does not contain a separable environment model.

## Learner architecture

The monolith contains, in one state transition:

1. Watkins critic state as the only learned Q/action-selection source;
2. deterministic count-memory LCB correction;
3. fixed-temperature sparsemax with Int8 dyadic temperature code `16`, representing `1/8` on the Q7 scale;
4. negative finite-rational q-log / Munchausen-style shaping;
5. learned sparsemax attention as representation state, not an independently optimized actor;
6. a four-dimensional Walsh-Hadamard representation boundary;
7. a custom recurrent GRU carrier with a state-independent hard-sign-derived gate;
8. finite-rational Mobius activation `x / (1 - x)` with an explicit singular boundary;
9. persistent recurrent parameter, noise, optimizer-token, and L2-token coordinates;
10. global F4-Int-U-style optimizer state with an explicit coupled L2 subtraction;
11. `NormPair` state carrying `l1` and `path` components;
12. deterministic Nat clock and complete `canonicalFullStep` composition.

This is learner-internal structure. None of these components is an environment definition.

## Watkins + sparsemax + LCB

`canonicalPolicy` consumes the Watkins critic and LCB count state, then applies `sparsemax2`.

The canonical sparsemax temperature is fixed:

`16 / 128 = 1 / 8`.

The checked finite regression laws are:

`(0,0) -> (64,64)`

`(1,0) -> (68,60)`

`(0,1) -> (60,68)`

The count-memory bonus table is finite and dyadic:

`127, 63, 31, 15, 7, 3, 1, 0`.

No statistical-confidence interpretation is attached to these finite corrections by theorem naming alone.

## Negative q-log / Munchausen-style boundary

`finiteQLog8` stores a finite numerator/denominator pair.

`negativeFiniteQLog8` negates the numerator exactly in the finite carrier.

`negativeFiniteQLogLaw` proves the corresponding constructor equality.

`canonicalQLogControlStep` and `canonicalQLogStep` place the shaping control and value inside the complete learner state transition.

The theorem surface does not claim a continuous-real q-log identity, Bayesian interpretation, or statistical optimality result.

## Learned attention is not an actor

`LearnedSparsemaxAttention` is learner representation state.

`canonicalPolicy-attention-invariant` proves that replacing the learned attention state leaves `canonicalPolicy` unchanged.

Therefore action selection has one learned Q source: Watkins. The learned attention block remains inside the learner and can have its own update through `attentionStep`, while its stored value does not create a second policy head through the canonical policy definition.

## Custom GRU boundary

The recurrent carrier is learner-internal:

`GRUState = hidden × matrices × noise × globalControl`.

The recurrent gate is state-independent in the sense formalized by:

`gateFromInput : Int8 -> Int8`.

Its hard-sign branch is the total finite three-way map:

`negative | zeroSign | positive`.

The gate codes are the finite Q7 representation of `(1 + hardSign) / 2`:

`-1 -> 0`, `0 -> 64`, `+1 -> 128`.

`gruStep` depends on the current input through that gate and through the finite Mobius activation. The persistent parameter/noise/global-control coordinates are structurally preserved.

`persistent-preservation` and `gruParameterPersistence` record those preservation laws.

This is a custom finite GRU-style recurrence. The theorem does not claim identity with every textbook GRU implementation.

## Mobius algebra

`mobiusRatio8-law` proves the exact rational boundary for inputs away from the singular point.

`mobiusSingularity` totalizes the singular input `x = 1` at an explicit finite boundary.

`MobiusAction` and `composeAction` provide an endomorphism carrier under ordinary composition, with:

`mobiusAssociativity`.

This is a genuine associative composition theorem. It does not imply that Walsh-Hadamard multiplication, sparsemax, or the entire learner update is itself an associative operation.

## Walsh-Hadamard boundary

The monolith includes the dimension-four Walsh basis and explicit Gram equalities:

`H₄ H₄ᵀ = 4 I`.

`walshOrthonormal` records the diagonal norm and off-diagonal orthogonality laws used by the finite boundary. The corresponding factor-of-two normalization is dyadic.

The canonical recurrent path lifts two action coordinates into the four-dimensional carrier before applying the Walsh transform.

## Global optimizer, L2, and norm-pair

`F4IntUState` is the optimizer state.

`F4IntUKernel.globalL2` is part of the optimizer kernel rather than a detached annotation.

`f4ThetaStep` performs the coupled update:

`base + gradient - L2 * base`,

followed by quantization and residual reconstruction.

`f4ParameterInvariant` proves the exact reconstruction equality supplied by the finite scalar contract.

`NormPair` stores the paired `l1` and `path` components inside the complete learner state.

The existence of these fields is not itself a convergence theorem. A global strict energy law still requires an explicit `FullLearnerCoerciveQuadratic` witness.

## Complete learner transition

`canonicalFullStep` updates, in one endogenous state transition:

`clock`

`Watkins`

`attention`

`GRU`

`optimizer`

`LCB counts`

`q-log control`

`q-log value`

while retaining the `NormPair` in the monolithic state boundary.

The component projection theorems are:

`canonicalFullStep-clock`

`canonicalFullStep-watkins`

`canonicalFullStep-attention`

`canonicalFullStep-gru`

`canonicalFullStep-optimizer`

`canonicalFullStep-counts`

`canonicalFullStep-qLog`

`canonicalFullStep-qLogControl`

`canonicalPersistentGRUPreservation` connects the actual canonical action-selection -> Walsh -> recurrent path with the persistent GRU theorem.

## Finite-cycle and convergence boundary

`LyapunovCertificate` expresses a Nat-valued strict-decrease law on an actual deterministic step function.

`noNontrivialFiniteCycle` proves arbitrary finite-cycle exclusion from that law.

`DeterministicLearnerCertificate` packages Lyapunov, decidable state equality, and a unique fixed target. `deterministicLearnerConvergence` derives exact finite arrival at that target.

`FullLearnerCoerciveQuadratic` is the whole-learner certificate boundary. `canonicalQuadraticDecay` exposes its strict-decrease premise, and `canonicalCoerciveNoCycle` feeds that concrete certificate into `noNontrivialFiniteCycle`.

The monolith does **not** claim that pessimistic initialization, sparsemax, LCB, Mobius activation, the optimizer, L2, norm-pair, or hard-sign alone imply a global Lyapunov inequality.

## Aperiodicity

`canonicalAperiodic` derives an exact no-return theorem from the Nat clock component of the augmented learner state.

This is an aperiodicity statement about the complete clocked learner carrier. It is not a stochastic Markov-chain aperiodicity theorem and does not establish convergence.

## Count-memory obstruction

`StrictCountSystem`, `count-two-step-increases`, and `noCountedTwoCycle` retain the finite count-memory obstruction family inside the monolith.

These are pure deterministic order theorems. They do not assert statistical validity of the LCB schedule.

## Architecture-class boundary

The monolith now proves an associative Mobius composition law and a concrete custom GRU recurrence, but it does **not** prove exact equivalence with Mamba, SSRN, Transformer, or the general RNN class.

Those would require explicit encoding/decoding maps and step-compatibility theorems for the relevant architecture. Associativity alone is insufficient evidence of architectural equivalence.

## Environment and statistics boundary

Environment semantics are intentionally external.

Statistical dependence is intentionally absent.

No theorem in this canonical source should be read as a claim of:

- almost-sure convergence;
- expected convergence;
- posterior correctness;
- confidence-bound calibration;
- empirical reward optimality;
- Watkins convergence to `Q*` for arbitrary environments;
- general regret bounds;
- Nash equilibrium;
- Pareto efficiency;
- minimax equality;
- Transformer/Mamba/SSRN equivalence.

## Redundancy pruning

The automatic redundancy audit is:

`.ci/discovery/PruneRedundantLearnerModules.hs`

It scans tracked Agda sources for imports of candidate learner modules. With no arguments it is a dry run. With `--apply`, it invokes `git rm` only on candidates whose module name has zero repository-local import users.

The policy deliberately protects unrelated modules rather than assuming that every historical learner file is redundant.

## Generated theorem status

`.ci/discovery/ExplorationTheoremGenerator.hs` checks the single canonical monolith for its required theorem symbols, invokes `agda --safe`, and writes the generated theorem-status report:

`Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`

Agda remains the proof authority. Haskell never upgrades a missing proof into a theorem.
