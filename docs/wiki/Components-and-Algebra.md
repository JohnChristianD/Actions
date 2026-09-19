# Components and Algebraic Structure

Last audited: 2026-09-19 against `main` at `d48e5cf6e3671f268440135f1acc32eeafb3d510`.

## Component graph

The canonical learner can be read as this typed composition:

```
CriticState + LCBCountState
        |
        v
     lcbScore
        |
        v
 ActionScore -> fixedTemperatureSparsemax
        |
        +--------------------+
        |                    |
        v                    v
 policy weight          learned attention
        |                    |
        v                    v
   finite Q-log        Walsh-Hadamard
        |                    |
        |                    v
        |             four-phase signed layer
        |                    |
        +---------+----------+
                  |
                  v
        canonical Watkins target
                  |
          +-------+--------+
          |                |
          v                v
     canonical GRU    canonical F4/L2
          |                |
          +-------+--------+
                  |
                  v
           FullLearnerState
                  |
                  v
          canonicalFullStep
                  |
                  +--> clock
                  +--> Watkins
                  +--> attention
                  +--> GRU
                  +--> optimizer
                  +--> counts
                  +--> Q-log
```

The endogenous feedback path is not an external search node. It is an explicit learner function:

```
attention mix
+ GRU hidden
+ F4/L2 state
+ Q-log control
+ Q-log value
        |
        v
canonicalEndogenousFeedback
        |
        v
canonicalWatkinsTarget
```

## Primary records and data

### Learner kernels

- `WatkinsKernel`
- `LCBCountKernel`
- `F4IntUKernel`
- `FullLearnerKernel`

### Learner state

- `WatkinsState`
- `CriticState`
- `LCBCountState`
- `LearnedSparsemaxAttention`
- `GRUState`
- `F4IntUState`
- `NormPair`
- `SignedQLogControl`
- `FullLearnerState`

### Finite closed-loop seam

The current closed-loop benchmark surface is:

- `CanonicalGamePorts.agda`
- `CanonicalFaithfulGameVariants.agda`
- `CanonicalClosedLoopBench.agda`

Its core records are `StepResult`, `ClosedLoopSpec`, `ClosedLoopRun`, and `ClosedLoopMetrics`.

There is no current `CanonicalClosedLoopInterface.agda`.

## Canonical theorem packaging

The active theorem monolith packages:

- `CanonicalAQLoopTheorem`
- `CanonicalConnectedCompositionTheorem`
- `FiniteTSTSEndogenousConnectedTheorem`
- `FiniteAttentionWatkinsGRUF4MediatorTheorem`
- `RecurrentAssociativeScanTheorem`
- `FiniteReservoirFaithfulnessTheorem`

and the underlying component laws for policy replacement, persistent GRU behavior, clock growth, count growth, sparsemax boundaries, and full-step projections.

The old `MercuryJaxtarAQCertificate` and `MercuryJaxtarAQEmergence` records belong to `GeneralFullCoupledTheoremsMonolith.agda`, not to the canonical theorem monolith.

## Algebraic forms actually used

### Finite carrier

`Int8` is a concrete wrapper around `Fin 256`.

Arithmetic is defined over finite natural-number codes. The code does not declare a generic abstract ring instance.

### Products

Nested products encode fixed-width vectors such as:

- `IntVec4`
- `WalshVec4`
- `Int8Vec4`
- `Int8WalshVec4`

### Closed finite alternatives

The implementation uses Agda data declarations for:

- `Signed`
- `HardSign8`
- `Phase4`
- `BoolLike`

Pattern matching gives total definitions over those finite alternatives.

### Endomorphism composition

`GRUAction` packages state-to-state functions.

`composeGRUAction` is associative, with `gruActionAssociativity` proved by definitional equality.

`identityGRUAction` is explicit. There is no imported standard-library `Monoid` instance for this surface.

### Equality and transport

The canonical proof language is dominated by:

- `_≡_`
- `refl`
- `sym`
- `trans`
- `cong`
- `subst`

This explains why many component projections and composition laws close by definitional equality.

### Finite witnesses and impossibility

The learner uses:

- `Fin` for finite carriers;
- `PowerOfFour` for the width-4 witness;
- `FiniteRational` for the exact finite Q-log representation;
- `⊥` for impossible cases.

## Semantic discovery algebra

The semantic-discovery tooling has a deliberately different status from the learner algebra.

The Mercury extractor derives a dependency graph from actual Agda declarations. The generic e-graph represents those extracted laws as symbolic expressions for normalization/regression purposes.

Mercury does not define the canonical learner's semantic alphabet, transformation grammar, or theorem meaning. Those originate in the Agda source and its extracted manifest.

## Faithfulness boundary

The finite environment layer is exact at the formal level:

- action domains are typed;
- states are explicit records;
- transitions are pure functions;
- finite map predicates are explicit;
- metrics derive from the formal episode result.

The repository does not claim external simulator equivalence without a separate correspondence proof.

## Generalized benchmark algebra

The generalized learner surface is independent:

`GeneralFullCoupledLearnerMonolith.agda` parameterizes action cardinality and uses list sorting/order structure for generalized policy selection.

`GeneralFullCoupledTheoremsMonolith.agda` packages generalized theorem statements and also contains the Mercury-named JAxtar certificate structures.

`GeneralClosedLoopBenchV2.agda` supplies generalized benchmark loops and ablations.

These are benchmark/general infrastructure, not replacements for the canonical learner theorem monolith.

## References

- [Agda standard library](https://agda.github.io/agda-stdlib/)
- [Agda User Manual](https://agda.readthedocs.io/)
- [Mercury documentation](https://mercurylang.org/documentation/documentation.html)
- [GNU Guix manual](https://guix.gnu.org/manual/en/guix/)

For the exact import inventory, see [Imports.md](Imports.md).

For theorem ownership, see [Theorem-Index.md](Theorem-Index.md).

For execution status, see [Verification-Status.md](Verification-Status.md).
