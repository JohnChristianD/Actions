# Canonical Learner Semantics

Last audited: 2026-09-19 against `d24c59101794ad3b6684889f709e46b5f0c10478`.

## 1. Bounded Int8 carrier

`CanonicalLearnerMonolith.agda` represents `Int8` as a record containing:

`code : Fin 256`.

The functions `int8OfNat`, `int8Add`, `int8Mul`, `int8Neg`, and `int8Sub` operate on the natural-number codes and reduce through the `Fin 256` boundary.

The implementation is therefore a finite code carrier with modular-style arithmetic. The file does not import a generic ring structure and does not establish generic ring laws for this carrier.

## 2. Policy and learner control

The policy surface is built from:

- `CriticState`
- `LCBCountState`
- `LCBCountKernel`
- `ActionScore`
- `Sparsemax2Pair`
- `fixedTemperatureSparsemax`

The canonical temperature code is `16`.

The learner also carries finite Q-log control and a finite rational representation:

`FiniteRational(sign, numerator, denominator)`.

The current theorem surface checks the Q-log representation law and several concrete sparsemax boundary cases.

## 3. Attention transform

`LearnedSparsemaxAttention` supplies two Int8 parameters.

The canonical attention path is:

`learnedSparsemaxAttentionWeights -> liftAttention -> walshHadamardApply -> phase4/walshRademacherRope4 -> readout`.

The Walsh structure is finite and explicit. The repository checks the 4-row Int8 Gram laws through `H4GramLaw` and provides a `PowerOfFour` witness for the width 4 boundary.

The phase system has four constructors and repeats after four steps.

This is an exact finite signed-permutation phase layer. It is not a sine/cosine numerical RoPE implementation.

## 4. GRU state and action composition

`GRUState` contains hidden state, matrices, noise, and global control.

`gruStep` changes the hidden coordinate while preserving the parameter-like coordinates.

The repository proves:

- `persistent-preservation`
- `gruParameterPersistence`
- `GRUEquivalent` reflexivity
- `gruStep-respects-equivalence`

It also defines `GRUAction`, `identityGRUAction`, and `composeGRUAction`. The action composition is associative by definitional equality in `gruActionAssociativity`. The identity action is present as an explicit component, while generic `Monoid` packaging is not imported.

## 5. F4-like optimizer component

The current learner uses:

`F4IntUState = (thetaQ, rTheta, eQ, rE, rL)`

with all fields carried as Int8.

The optimizer kernel separately contains:

`globalL2 : Int8`.

This is distinct from the older wiki's six-state `CanonicalCoupledF4Learner.agda`. That older surface is no longer the current canonical learner.

The current optimizer step is supplied through `f4ThetaStep` and connected to the canonical signal by `canonicalOptimizerStep-qMunchausen-L2`.

## 6. Full learner state

`FullLearnerState` contains:

1. clock
2. Watkins state
3. learned sparsemax attention
4. GRU state
5. optimizer state
6. norm pair
7. LCB counts
8. signed Q-log control
9. finite Q-log value

`canonicalFullStep`:

1. increments the clock;
2. updates Watkins state;
3. updates the attention component;
4. updates GRU state from canonical signal plus canonical attention mix;
5. updates the optimizer from the canonical Watkins signal;
6. preserves the norm pair;
7. updates LCB counts;
8. updates Q-log control and value.

Projection lemmas `canonicalFullStep-*` expose these components directly.

## 7. Closed-loop environment interface

`CanonicalClosedLoopInterface.agda` adds:

`ClosedLoopEnv A S`
`ClosedLoopAgent A`
`EpisodeResult S`
`EpisodeMetrics S`
`BenchSpec A S`

The episode runner composes environment transitions and learner updates explicitly.

The metrics surface defines return, reference return, truncated regret, success, steps, and observed final state.

This closes the type-level seam between a canonical learner state and a finite environment, without claiming external simulator equivalence.

## 8. Exact finite environment variants

`CanonicalFaithfulGameVariants.agda` gives exact boolean predicates for finite Toy Maze and FourRooms layouts.

These are useful as finite semantic ports because their cells and boundaries are represented directly in Agda.

They should be read as exact finite contracts, not as empirical replicas of a larger simulator.

## 9. Structural algebra

The current source uses several algebraic patterns without importing broad abstract-algebra interfaces:

- bounded carrier: `Int8` over `Fin 256`;
- products: tuples and nested products via `Data.Product`;
- finite sums: Agda data declarations such as `Signed`, `HardSign8`, and `Phase4`;
- records: kernels, states, certificates, and benchmark specifications;
- endomorphism composition: `GRUAction`;
- equality transport: `_≡_`, `cong`, `subst`, `trans`, `sym`;
- finite witnesses: `Fin`, `PowerOfFour`, and direct finite-code equations;
- impossible cases: `⊥`.

The repository does not presently import `Algebra.*` typeclass-like structures for the canonical learner. Its algebra is mostly concrete and definitionally checked.

For the standard library semantics, see:
- [Agda standard library 2.3](https://agda.github.io/agda-stdlib/v2.3/)
- [Agda User Manual 2.8.0](https://agda.readthedocs.io/en/v2.8.0/)
- [Agda safe mode](https://agda.readthedocs.io/en/v2.8.0/language/safe-agda.html)
