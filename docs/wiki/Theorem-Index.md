# Theorem Index

Last audited: 2026-09-19.

## A. Canonical theorem monolith

Single active source:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

### Core carrier and policy laws

- `int8Roundtrip`
- `temperatureCodeLaw`
- `temperatureTieLaw`
- `temperaturePositiveUnitLaw`
- `temperatureNegativeUnitLaw`
- `negativeFiniteQLogLaw`

### Walsh / phase laws

- `walshHadamardOrthogonality4`
- `canonicalWalshWidth-power4`
- `phase4-period4`
- `walshRademacherRope4-period4`
- `canonicalAttentionMix-clock-period4`

### GRU laws

- `persistent-preservation`
- `gruParameterPersistence`
- `gruEquivalent-refl`
- `gruStep-respects-equivalence`
- `gruActionAssociativity`
- `gruInputActionAssociativity`

### Full-step laws

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

### Connected composition

`CanonicalAQLoopTheorem` packages:

1. policy composition;
2. learned-attention composition;
3. shared Watkins signal;
4. GRU/attention coupling;
5. F4 signal coupling;
6. endogenous Watkins target composition.

`CanonicalConnectedCompositionTheorem` packages:

- the A/Q loop;
- phase periodicity;
- clock growth;
- finite-cycle exclusion.

The current cycle laws are:

- `canonicalClockAfter`
- `canonicalAperiodic`
- `canonicalNoNontrivialFiniteCycle`

### Finite EvoSAX OpenAI-ES composition

The monolith now contains the first discovered meta-search composition certificate:

- `finiteOpenESPlus`
- `finiteOpenESMinus`
- `finiteOpenESObjective`
- `finiteOpenESAntitheticGradient`
- `finiteOpenESTell`
- `finiteOpenESProbe`
- `finiteOpenESComposeStep`
- `FiniteOpenESCanonicalCompositionTheorem`
- `finite-openES-canonical-composition-theorem`
- `finite-openES-discovered-evaluator-boundary`

This is a finite symbolic specialization of EvoSAX `Open_ES`: an antithetic two-probe `ask/evaluate/tell` loop over the existing `F4IntUState`, with the canonical Agda learner as the evaluator. It is not a floating-point/JAX numerical equivalence claim.

The new composition theorem proves that the optimizer variation can feed the existing executable learner while preserving the norm-pair observable and the GRU persistent quotient, and that the current policy remains invariant under an optimizer-only probe replacement.

### Mercury / JAxtar A/Q certificate

The same theorem monolith now contains:

- `AQChannel`
- `AQOp`
- `aqSource`
- `aqTarget`
- `aqPath`
- `MercuryJaxtarAQCertificate`
- `MercuryJaxtarAQEmergence`
- `mercury-jaxtar-aq-certificate`
- `mercury-jaxtar-aq-emergence`

This gives one Agda source of truth for the finite A/Q graph that Mercury discovers and verifies.

The certificate is exact symbolic composition. It is not a proof that the external JAxtar implementation, a trained neural search system, or an external simulator is observationally equivalent.

## B. Closed-loop faithfulness boundary

`CanonicalClosedLoopInterface.agda` supplies the environment/agent/episode contract.

`CanonicalFaithfulGameVariants.agda` supplies exact finite Toy Maze and FourRooms predicates.

These prove structural closure of the formal interfaces, not external behavioral equivalence.

## C. Legacy/general theorem substrate

`GeneralFullCoupledTheoremsMonolith.agda` remains available for generic theorem infrastructure and conditional certificates.

It is not part of the current canonical discovery entrypoint.

`MonolithCompositeReservoirTheorem.agda` remains a legacy conditional certificate adapter. It is intentionally excluded from the canonical theorem gate because its certificate fields are assumptions supplied by callers, not unconditional learner theorems.

## D. Verification rule

A theorem counts as currently verified only after the module owning it passes the current Guix/Agda `--safe` lane.

A record field is not counted as a derived theorem merely because the record type names it.
