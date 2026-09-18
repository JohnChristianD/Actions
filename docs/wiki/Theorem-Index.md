# Theorem Index

Last audited: 2026-09-19 against `d24c59101794ad3b6684889f709e46b5f0c10478`.

## A. Canonical learner laws

### Finite carrier and sparse policy

- `int8Roundtrip`
- `temperatureCodeLaw`
- `temperatureTieLaw`
- `temperaturePositiveUnitLaw`
- `temperatureNegativeUnitLaw`
- `negativeFiniteQLogLaw`

### Walsh and phase layer

- `walshHadamardOrthogonality4`
- `canonicalWalshWidth-power4`
- `phase4-period4` in the theorem monolith
- `walshRademacherRope4-period4` in the theorem monolith

### GRU structure

- `persistent-preservation`
- `gruParameterPersistence`
- `gruEquivalent-refl`
- `gruStep-respects-equivalence`
- `gruActionAssociativity`
- `gruInputActionAssociativity`

### Canonical full-step projections

- `canonicalFullStep-clock`
- `canonicalFullStep-watkins`
- `canonicalFullStep-attention`
- `canonicalFullStep-gru`
- `canonicalFullStep-optimizer`
- `canonicalFullStep-norm`
- `canonicalFullStep-counts`
- `canonicalFullStep-qLog`
- `canonicalFullStep-qLogControl`
- `canonicalTotalCountStep`
- `canonicalNoFixedPoint`

These are structural projection/equality theorems. They describe the current function definitions; they do not establish an external benchmark optimum.

## B. Composed A/Q theorem

`CanonicalAQLoopTheorem` packages six component relationships:

1. policy composition;
2. learned-attention composition;
3. shared Watkins signal;
4. GRU/attention coupling;
5. F4 signal coupling;
6. endogenous Watkins target composition.

The constructor `canonical-aq-loop-theorem` supplies all six fields with definitionally equal proofs.

## C. Connected composition theorem

The latest commit adds:

- `canonicalClockAfter`
- `canonicalAperiodic`
- `canonicalNoNontrivialFiniteCycle`

and packages them in `CanonicalConnectedCompositionTheorem` with:

`aqLoop`
`ropePhasePeriod`
`clockGrowth`
`finiteCycleExclusion`.

This is the current composed theorem boundary.

"Complete" here means the declared fields of this record have been filled by exact source-level proofs. It does not mean every conceivable property of the learner has been proved.

## D. Mercury typed composition certificate

`GeneralFullCoupledTheoremsMonolith.agda` contains a typed A/Q discovery certificate:

- `AQChannel`
- `AQOp`
- `aqSource`
- `aqTarget`
- `MercuryJaxtarAQCertificate`
- `MercuryJaxtarAQEmergence`

The path joins connect critic -> sparsemax -> attention, attention -> Walsh/phase -> recurrent signal, and sparsemax -> Q-log bias -> Watkins signal.

The certificate laws are exact finite symbolic equations. Its current fields should not be interpreted as a statistical or causal-fidelity claim about a trained model.

## E. Learner faithfulness / closed loop

`CanonicalClosedLoopInterface.agda` proves concrete structural laws such as:

- action indices stay within `Fin A`;
- binary learner steps advance the clock;
- regret is the declared truncated subtraction;
- the closed-loop interface composes an environment step with a typed learner update.

`CanonicalFaithfulGameVariants.agda` supplies exact finite Toy Maze and FourRooms layout predicates.

The current surface does not prove:

- equivalence with an external Gymnax implementation;
- equality with CleanRL behavior;
- optimality on an external environment;
- empirical generalization;
- latent-model or cognitive "faithfulness".

## F. Finite-state / observation boundary

The general theorem monolith also derives a strong finite-carrier obstruction from the learner's unbounded natural-number clock. In particular, a finite observation carrier cannot admit a left inverse for the full learner state under the stated assumptions.

This is a theorem about the formal state representation. It is not a statement about every possible learned model.

## G. Historical theorem pages

The older pages for `CanonicalCoupledF4Learner.agda` and `CanonicalCoupledCompositionTheorems.agda` describe an earlier semantic surface. They remain useful as historical records but are not the current canonical entrypoint.

For current proof status, see `Verification-Status.md`.
