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
3. fixed-temperature sparsemax over the Int8 carrier;
4. a finite negative q-log/Munchausen-style shaping carrier;
5. learned sparsemax attention as representation state, not the action-selection source;
6. a four-coordinate Walsh-labelled representation path;
7. a custom hard-sign input-gated GRU-style recurrence;
8. a finite rational activation boundary named `mobiusActivation8`;
9. persistent recurrent matrices, noise, and global optimizer/L2 control coordinates;
10. an F4-Int-U-style optimizer state with explicit global L2 correction;
11. `NormPair` storage containing `l1` and `path` coordinates;
12. a deterministic Nat clock and complete `canonicalFullStep` map.

## Int8 carrier and exact pure-quantized counts

`Int8` wraps `code : Fin 256`, so the quantized scalar carrier has exactly **256 values**.

The current `GRUState` has nine independent Int8 coordinates:

- hidden state: 1;
- recurrent matrices: 3;
- recurrent noise: 3;
- global optimizer/L2 control: 2.

Thus a purely Int8-counted GRU state space has `256^9 = 2^72` configurations.

The relation

`GRUEquivalent s t = persistentGRU s = persistentGRU t`

forgets only the hidden coordinate. Therefore each GRU equivalence fibre has **256 = 2^8** states, and the quotient has `256^8 = 2^64` equivalence classes.

For a pure-Int8 combined `GRUCriticWH8State`, the code counts:

- GRU: 9 coordinates;
- critic: 2 coordinates;
- Walsh carrier: 4 coordinates.

Total: **15 Int8 coordinates**, hence `256^15 = 2^120` combined configurations. The quotient relation keeps the persistent GRU projection, critic, and Walsh coordinates fixed, so it has **14 coordinates**, `256^14 = 2^112` equivalence classes, again with hidden fibres of size 256.

`WalshVec4` in the actual recurrence path is still represented by `HalfInt` natural numerators. `Int8WalshVec4` is the explicit pure-Int8 counting carrier used for the state-count theorem. The code therefore does not silently claim that the existing `HalfInt` path is finite.

`int8OfNat` reduces natural inputs modulo 256 through `Data.Nat.DivMod`. This is finite-carrier normalization, not general rational-number division.

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

## GRU equivalence class and why a non-ring algebra is useful

`GRUState` is not given ring operations. That is deliberate: the useful composition law is on **transition operators**, not on the state carrier itself.

`GRUAction` is the endomorphism carrier `GRUState -> GRUState`. `composeGRUAction` is ordinary function composition, so it is associative by definitional equality. The identity operator is `identityGRUAction`.

This produces a monoid of recurrent transition actions even though the underlying quantized arithmetic is not being declared a mathematical ring. The benefit is exact, order-preserving regrouping of transition composition. Associativity is enough for prefix trees, segmented scans, and balanced reductions. Commutativity is neither assumed nor needed.

The custom recurrence additionally factors through the persistent projection:

`persistentGRU (gruStep s x) = persistentGRU s`.

Consequently, `gruStep-respects-equivalence` proves that the input transition descends to the quotient by `GRUEquivalent`. The hidden coordinate can evolve inside each equivalence fibre while matrices, noise, and global control remain invariant.

This is the algebraic reason the GRU belongs inside the learner composition: the learner can compose and scan its recurrent operators without pretending the entire architecture forms a ring.

## Associative scan theorem

For each Int8 input `x`, `inputGRUAction x` is an endomorphism of `GRUState`.

`gruInputActionAssociativity` proves:

`(F_x ∘ F_y) ∘ F_z = F_x ∘ (F_y ∘ F_z)`

when both sides are applied to a state. This is the exact local law required to regroup a sequential composition in an associative scan. The order of inputs is preserved.

The theorem does **not** say that the nonlinear hidden update is linear, commutative, or itself an algebraic semigroup under pointwise state arithmetic. The monoid is the transition-action layer.

## Mobius associative scan

`mobiusActivation8` is an exact alias of the finite `mobiusRatio8` carrier.

The current `mobiusFormula` is a finite rational encoding by sign/numerator/denominator cases. It is not a general real Möbius transform `(a x + b)/(c x + d)`.

`MobiusAction` again uses endofunction composition. `mobiusAssociativity` is exact, and `gruMobiusAssociativeScan` exposes the same associative regrouping for the activation-derived actions produced from the custom GRU channel.

Therefore the strongest accurate statement is: the implementation has **Möbius-labelled finite activation plus associative action composition**, not a proof that the complete GRU update is itself a classical Möbius transformation.

## Hard sparsity under NormPair + F4 + coupled L2

`HardSparseLeft` and `HardSparseRight` define exact one-hot sparsemax outputs in the finite carrier. Concrete exact witnesses are `hardSparseLeft16`, `hardSparseRight16`, `hardSparseLeft15`, and `hardSparseRight15`.

`NormPair` stores the finite L1/path coordinates and `normPairWeightPlusOne` adds the explicit `+1` offset to their derived carrier.

`F4IntUState` stores the custom optimizer coordinates. `F4IntUKernel.globalL2` enters the optimizer through `l2Correction` inside `f4ThetaStep`.

The theorem `hardSparse-composition-normPair-F4-L2` states the exact composition invariant:

if the current canonical policy is already in `HardSparseLeft`, replacing the `NormPair` and optimizer state, with the optimizer carrying its global L2 coordinate, leaves that hard-sparse policy result unchanged.

The proof is deduction by equality composition from `canonicalPolicy-norm-invariant` and `canonicalPolicy-optimizer-invariant`.

This is a structural invariance theorem. It does not claim that arbitrary Watkins or LCB evolution can never move a trajectory across the sparsemax boundary, and it does not claim that an analytic L1/path norm controls sparsity.

## Walsh-labelled boundary

The current four natural-number rows are:

`row0 = (1,1,1,1)`

`row1 = (1,0,1,0)`

`row2 = (1,1,0,0)`

`row3 = (1,0,0,1)`.

`walshOrthonormal` proves only the diagonal self-dot laws `4,2,2,2` in this representation. It does **not** prove the full H4 identity `H4 H4^T = 4I`.

`liftAttention` and `walshHadamardApply` remain the exact attention-to-recurrent representation path.

## Global optimizer and NormPair

`f4ParameterInvariant` is a constructor equality reconstructing the updated theta coordinate with the global L2 correction.

`NormPair` is a finite two-coordinate storage record. `normPairWeight` and `normPairWeightPlusOne` are the exact finite derived carriers. No analytic real-valued norm theorem is inferred from those names.

## Complete learner transition

`canonicalFullStep` updates, in one deterministic endogenous map:

`clock, Watkins, attention, GRU, optimizer, LCB counts, q-log control, q-log value`

while retaining `NormPair`.

The projection theorems are the `canonicalFullStep-*` family, with `canonicalFullStep-norm` additionally proving exact NormPair preservation.

`canonicalRecurrentInput-law` exposes the actual attention -> Walsh -> GRU input expression, and `canonicalPersistentGRUPreservation` proves persistence on that full composed path.

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

## Literature-algebra correspondences

Several published lines of work are structurally adjacent to the canonical action-composition view, without making it an equivalence claim.

- Martin and Cundy, **Parallelizing Linear Recurrent Neural Nets Over Sequence Length** (ICLR 2018, arXiv:1709.04057) use parallel scan for recurrences with linear sequential dependencies. The canonical learner's `gruInputActionAssociativity` supplies an analogous regrouping law at the transition-operator level, but the custom GRU here is not thereby a linear recurrence. https://arxiv.org/abs/1709.04057
- Maleki and Burtscher, **Automatic Hierarchical Parallelization of Linear Recurrences** (ASPLOS 2018) study associative-style parallel evaluation of linear recurrences on massively parallel hardware. The shared algebraic idea is regroupable recurrence composition, not identical arithmetic. DOI: https://doi.org/10.1145/3173162.3173168
- Ali, Zimerman, and Wolf, **The Hidden Attention of Mamba Models** (2024) describe selective SSMs as parallel-scan models and analyze their attention interpretation. This is a useful architectural analogue for the learner's attention-to-recurrence path, not a claim that the learner is Mamba. https://arxiv.org/abs/2403.01590
- Becker, Freymuth, and Neumann, **KalMamba: Towards Efficient Probabilistic State Space Models for RL under Uncertainty** (2024) explicitly uses parallel associative scanning for state-space inference in an RL setting. This is close in scan semantics but uses different state-transition algebra. https://arxiv.org/abs/2406.15131
- Weissenborn and Rocktäschel, **MuFuRU: The Multi-Function Recurrent Unit** (2016) frames recurrent computation in terms of gated composition operations. It motivates thinking about the recurrence as composition of learned operators, but does not supply the exact finite quotient/scan theorem proved here. https://arxiv.org/abs/1606.03002
- Jones, Swan, and Giansiracusa, **Algebraic Dynamical Systems in Machine Learning** (2024) develops an algebraic treatment of dynamical models and emphasizes compositional structure. This is a useful conceptual correspondence for the learner's transition monoid. DOI: https://doi.org/10.1007/s10485-023-09762-9

The code therefore has a clean literature-aligned interpretation as an endomorphism-composition system with a persistent-state quotient, rather than as an undocumented claim of equivalence to a standard GRU, Mamba, SSRN, Transformer, or ring-valued neural algebra.

## What is proved and what is not

The maintained safe surface proves finite-carrier algebra, learner component projections, policy-separation properties, persistent-GRU quotient compatibility, associative transition composition, Mobius-labelled activation composition, hard-sparsity witnesses, the NormPair/F4/L2 composition invariant, optimizer reconstruction, and contradiction-based noncycle facts.

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
- a full H4 orthogonality identity for the current Walsh rows;
- a global strict Lyapunov decrease theorem for the clocked learner.

## Redundancy pruning

The automated audit is `.ci/discovery/PruneRedundantLearnerModules.hs`.

Default mode is dry-run. `--apply` deletes only candidates whose module name has zero repository-local import users.

Known noncanonical language or oracle artifacts are not needed by the canonical Agda theorem surface. The maintained cross-language oracle is Haskell; redundant Elixir and Ruby rational-oracle files were removed from this branch. No Python, Bash, C, C++, JVM, C#, or actual Clojure source file is part of the current canonical theorem surface.

## Generated theorem status

`.ci/discovery/ExplorationTheoremGenerator.hs` checks the required theorem symbols in the single canonical monolith, runs `agda --safe`, and writes `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`.

Haskell reports discovery status only. Agda proof terms remain authoritative.
