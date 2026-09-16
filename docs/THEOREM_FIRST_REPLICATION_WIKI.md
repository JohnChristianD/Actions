# Theorem-first canonical learner wiki

Authority: Agda `--safe` proof terms. Haskell discovery and redundancy auditing are automation only.

## Canonical source

`Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

The monolith has no project-local Agda imports. The learner state is endogenous: there is no environment type, reward process, transition-probability space, posterior sampler, replay buffer, or statistical-limit assumption.

The environment remains external. An application supplies the finite learner kernel.

## Learner architecture

The single-file learner contains:

1. a Watkins-style critic state and greedy trace kernel;
2. deterministic count-memory LCB correction;
3. fixed-temperature sparsemax over the Int8 Q7-style carrier;
4. a finite negative q-log/Munchausen-style shaping carrier;
5. learned sparsemax attention as representation state, not the action-selection source;
6. a four-coordinate Walsh-labelled representation boundary;
7. a custom hard-sign input-gated GRU-style recurrence;
8. a finite rational activation boundary named `mobiusActivation8`;
9. persistent recurrent matrices, noise, and global optimizer/L2 control coordinates;
10. an F4-Int-U-style optimizer state with explicit global L2 correction;
11. `NormPair` storage containing `l1` and `path` coordinates;
12. a deterministic Nat clock and complete `canonicalFullStep` map.

## Int8 carrier and exact state count

`Int8` is a record containing `code : Fin 256`.

Therefore the carrier has exactly **256 distinct values**. `int8StateSpace` exposes the underlying `Fin 256` carrier directly.

`int8OfNat` reduces arbitrary natural inputs modulo 256 through `Data.Nat.DivMod`. This division/modulo machinery is for finite carrier normalization, not rational-number division.

The monolith does not import the older project-local exact-rational modules. The local `FiniteRational` record is a finite triple of natural `sign`, `numerator`, and `denominator` fields, with no rational division operation. Adding full exact rational division would require extra integer/rational algebra and would enlarge the trusted import surface.

## Watkins + sparsemax + LCB

`canonicalPolicy` consumes Watkins critic values and LCB count state, then applies fixed-temperature sparsemax.

The temperature is represented by Int8 code `16`; the regression surface establishes the implemented finite laws:

`(0,0) -> (64,64)`

`(1,0) -> (68,60)`

`(0,1) -> (60,68)`

The finite LCB bonus table is:

`127, 63, 31, 15, 7, 3, 1, 0`.

These are exact finite-carrier computations. No statistical-confidence guarantee is inferred from the table alone.

## Negative q-log / Munchausen-style boundary

`finiteQLog8` stores a finite rational-shaped triple. `negativeFiniteQLog8` constructs a related finite negative-sign carrier, and `negativeFiniteQLogLaw` proves its constructor-level equality.

`canonicalQLogControlStep` derives its signed coefficient from the current policy, while `canonicalQLogStep` stores the finite q-log value in the complete state.

No continuous-real logarithm identity, Bayesian interpretation, or statistical optimality theorem is claimed by these names.

## Learned attention is not an actor

`LearnedSparsemaxAttention` is learner representation state.

`canonicalPolicy-attention-invariant` proves that replacing attention state leaves action selection unchanged.

At the same time, `canonicalGRUStep` consumes the learned attention representation through the Walsh-labelled boundary. Thus attention is computationally active in the recurrent path without becoming a second action-selection source.

## What the custom GRU buys theoremically

`GRUState` contains hidden state, recurrent matrices, noise coordinates, and global optimizer/L2 control coordinates.

`gateFromInput` depends only on the current Int8 input. The hard-sign branch is `negative | zeroSign | positive`, with gate codes `0`, `64`, and `128`.

The decisive theorem is the persistent projection:

`persistentGRU (gruStep s x) = persistentGRU s`.

This gives a canonical equivalence relation:

`GRUEquivalent s t = persistentGRU s = persistentGRU t`.

`gruStep-respects-equivalence` proves every input transition respects this relation. Thus the recurrence factors through equivalence classes of states having the same persistent parameter/noise/control projection. Each input induces an endomorphism of those equivalence classes.

`GRUAction` and `composeGRUAction` give ordinary function composition, with `gruActionAssociativity` proved definitionally. The induced input actions satisfy `gruInputActionAssociativity`.

This is the theoremically useful part of the custom GRU: persistent coordinates become invariants of the recurrent dynamics, while hidden-state motion remains state-dependent inside each equivalence fibre.

## Associative scan interpretation

A sequence of inputs is mapped to a composition of the corresponding `inputGRUAction` endomorphisms. Because function composition is associative, a prefix tree, segmented scan, or balanced reduction may regroup compositions without changing the resulting endomorphism.

The source proves associativity directly for three inputs through `gruInputActionAssociativity`.

This is an algebraic scan theorem about the transition operators. It does not assert that the hidden update is commutative, nor that arbitrary learned parameters can be parallelized without preserving composition order.

## Mobius qualification

`mobiusActivation8` is an exact alias of the finite `mobiusRatio8` carrier.

The current `mobiusFormula` is a finite rational encoding by sign/numerator/denominator cases. It is not a general real Möbius transform of the form `(ax+b)/(cx+d)`.

`MobiusAction` is an ordinary finite endofunction carrier with associative function composition. `mobiusAssociativity` is therefore an exact composition theorem.

`mobiusActivationAction` exposes one activation-derived endofunction per input, and `gruMobiusActivationAssociativity` proves associativity for those activation-channel actions.

Accordingly, the whole `gruStep` should not be described as itself being a Möbius transformation.

## Walsh-labelled boundary

The current four rows are natural-number representatives:

`row0 = (1,1,1,1)`

`row1 = (1,0,1,0)`

`row2 = (1,1,0,0)`

`row3 = (1,0,0,1)`.

`walshOrthonormal` proves only their diagonal self-dot laws `4,2,2,2` in this representation. It does **not** prove the full H4 orthogonality identity `H4 H4^T = 4I`.

The implementation still exposes `liftAttention` and `walshHadamardApply` as the exact representation path into the GRU.

## Global optimizer and NormPair

`F4IntUState` is the optimizer state. `F4IntUKernel.globalL2` enters `f4ThetaStep` through the exact finite correction `l2Correction`.

`f4ParameterInvariant` is a constructor equality reconstructing the updated theta coordinate.

`NormPair` stores two finite coordinates, `l1` and `path`, with derived carriers `normPairWeight` and `normPairWeightPlusOne`. The source does not define an analytic L1 norm or a path norm over an arbitrary parameter space.

`canonicalPolicy-norm-invariant` and `canonicalPolicy-optimizer-invariant` show that these state components are policy-independent at a fixed learner state.

## Hard sparsity theorem

`HardSparseLeft` and `HardSparseRight` define exact one-hot sparsemax outputs in the finite carrier.

The source proves concrete witnesses `hardSparseLeft32` for score codes `(32,0)` and `hardSparseRight32` for score codes `(0,32)`.

The theorem `hardSparse-norm-optimizer-invariant` proves that when a canonical policy is already in the `HardSparseLeft` class, changing only `NormPair` and optimizer state cannot destroy that policy result.

This is a composition theorem for those coordinates, not a claim that Watkins/LCB updates can never move a trajectory out of the sparse region.

## Complete learner transition

`canonicalFullStep` updates, in one deterministic endogenous map:

`clock, Watkins, attention, GRU, optimizer, LCB counts, q-log control, q-log value`

while retaining `NormPair`.

The projection theorems are:

`canonicalFullStep-clock`

`canonicalFullStep-watkins`

`canonicalFullStep-attention`

`canonicalFullStep-gru`

`canonicalFullStep-optimizer`

`canonicalFullStep-counts`

`canonicalFullStep-qLog`

`canonicalFullStep-qLogControl`.

`canonicalRecurrentInput-law` exposes the actual attention -> Walsh -> GRU input expression, and `canonicalPersistentGRUPreservation` proves the persistent GRU projection is unchanged on that composed path.

## Unconditional contradiction and negation theorems

No coercive or Lyapunov certificate premise is needed for the current cycle exclusions.

Every `canonicalFullStep` applies `suc` to the Nat `clock`. Hence `canonicalStep-not-fixed` follows by applying `clock` and reducing to the contradiction `n + 1 = n`.

`clockAfter` proves exact iteration:

`clock (iterateCanonical K n s) = clock s + n`.

From that, `canonicalAperiodic` proves `iterateCanonical K (suc n) s != s`.

`canonicalOrbitNonFixed` transfers the one-step contradiction to every orbit point, and `canonicalNoNontrivialFiniteCycle` discharges a hypothetical finite return directly into `⊥`.

No environment assumption, stochastic assumption, convergence assumption, or Lyapunov witness is used.

## Count-memory contradiction

`canonicalTotalCountStep` proves `totalCount (canonicalFullStep K s) = suc (totalCount s)`.

Applying `totalCount` to a hypothetical two-cycle produces `suc (suc n) = n`, discharged by `suc-suc-not-self` in `canonicalNoCountedTwoCycle`.

## What is proved and what is not

The maintained safe surface proves finite-carrier algebra, learner component projections, policy-separation properties, persistent-GRU quotient compatibility, associative transition composition, hard-sparsity witnesses, optimizer reconstruction, and contradiction-based noncycle facts.

It does not claim:

- convergence to `Q*` for arbitrary environments;
- almost-sure or expected convergence;
- LCB calibration or confidence correctness;
- posterior-sampling equivalence;
- regret or global optimality;
- Nash, Pareto, or minimax equivalence;
- equivalence to Mamba, SSRN, Transformer, or a generic textbook GRU;
- a continuous-real rational-division implementation;
- a global analytic L1/path norm theorem;
- a global strict Lyapunov decrease theorem for the clocked learner.

## Redundancy pruning

The automated audit is `.ci/discovery/PruneRedundantLearnerModules.hs`.

Default mode is dry-run. `--apply` deletes only candidates whose module name has zero repository-local import users.

Known noncanonical language or oracle artifacts are not needed by the canonical Agda theorem surface. The maintained cross-language oracle is Haskell; redundant Elixir and Ruby rational-oracle files were removed from this branch. No Python, Bash, C, C++, JVM, C#, or actual Clojure source file is part of the current branch surface.

## Generated theorem status

`.ci/discovery/ExplorationTheoremGenerator.hs` checks the required theorem symbols in the single canonical monolith, runs `agda --safe`, and writes `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`.

Haskell reports discovery status only. Agda proof terms remain authoritative.
