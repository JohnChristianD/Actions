# Theorem Index

Last audited: 2026-09-19 against `main` after the automated e-graph correction.

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

### Walsh and phase laws

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
- `canonicalStep-not-fixed`
- `canonicalNoFixedPoint`
- `canonicalTotalCountIterate2`
- `canonicalNoCountedTwoCycle`

### Canonical connected composition

`CanonicalAQLoopTheorem` packages:

1. policy composition;
2. learned attention composition;
3. shared Watkins signal;
4. GRU/attention coupling;
5. F4/L2 signal coupling;
6. endogenous Watkins target composition.

`CanonicalConnectedCompositionTheorem` packages:

- the A/Q loop;
- phase periodicity;
- clock growth;
- finite-cycle exclusion.

The associated cycle laws are:

- `canonicalClockAfter`
- `canonicalAperiodic`
- `canonicalNoNontrivialFiniteCycle`

### Existing TSTS endogenous connected theorem

The TSTS structure remains an existing canonical theorem surface:

- `FiniteTSTSBranch`
- `FiniteTSTSPosterior`
- `finiteTSTSSelect`
- `finiteTSTSSelectedProbe`
- `finiteTSTSSelectedTarget`
- `finiteTSTSReward`
- `finiteTSTSPosteriorUpdate`
- `finiteTSTSNextPosterior`
- `finiteTSTSClosedStep`
- `FiniteTSTSEndogenousConnectedTheorem`
- `finite-tsts-endogenous-connected-theorem`

Its presence does not imply that TSTS is the semantic definition of the canonical learner. The discovery generator for TSTS has been removed.

### Intrinsic attention-mediator theorem

The active learner-local mediator theorem is:

- `FiniteAttentionWatkinsGRUF4MediatorTheorem`
- `finite-attention-watkins-gru-f4-mediator-theorem`

It formalizes the chain:

```
attention replacement
    -> policy/count/Q-log invariance
    -> endogenous Watkins expansion
    -> shared GRU and F4 consumption
```

and also carries NormPair/persistent-GRU preservation through the canonical full step.

The theorem itself does not depend on a Mercury search procedure.

### Recurrent scan theorem class

The theorem monolith packages:

- `RecurrentAssociativeScanTheorem`
- `canonicalGRU-recurrent-associative-scan-theorem`

over the generic `RecurrentNetwork` abstraction exposed by the learner monolith.

The split theorem holds for arbitrary natural prefix lengths. It is a structural law of the executable recurrence.

### Finite reservoir boundary

The theorem monolith also contains:

- `FiniteReservoirFaithfulnessTheorem`
- `finiteReservoirFaithfulnessTheorem`

This is a finite/discrete faithfulness boundary based on an explicit left-inverse/injectivity/readout factorization. It is not a continuous reservoir-universality theorem.

## B. Learner-local replacement algebra

The canonical theorem monolith defines:

- `LearnerReplacement`
- `applyLearnerReplacement`
- `applyLearnerReplacements`
- `canonicalPolicy-learnerReplacement-invariant`
- `canonicalPolicy-learnerReplacement-composition`
- `canonicalNormPair-afterFullStep-iterate`
- `canonicalPersistentGRU-afterFullStep-iterate`

These are semantic laws over actual learner state replacement. They are part of the theorem source, not a Mercury-generated symbolic vocabulary.

## C. Generated semantic-discovery artifact

The current generated file is:

`Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda`

It has `{-# OPTIONS --safe #-}` and currently exposes four source-owned theorem projections generated from the shared semantic manifest:

- `generatedSemanticDerived0` -> `canonicalStep-not-fixed`
- `generatedSemanticDerived1` -> `clockAfter`
- `generatedSemanticDerived2` -> `canonicalAperiodic`
- `generatedSemanticDerived3` -> `canonicalNoCountedTwoCycle`

These are source-owned semantic projections; the e-graph quotient count is recorded alongside them, and they are not automatically promoted into `TheoremsMonolith.agda`.

The name "NovelLearnerTheorems" is retained for CI continuity, but the present generator does not synthesize a novel transformation grammar.

## D. Closed-loop formal boundary

`CanonicalGamePorts.agda` defines exact finite transition ports.

`CanonicalFaithfulGameVariants.agda` defines exact Toy Maze and FourRooms predicates.

`CanonicalClosedLoopBench.agda` defines `ClosedLoopSpec`, `ClosedLoopRun`, and `ClosedLoopMetrics` and composes those finite ports with the canonical learner.

These are structural formal contracts, not external simulator equivalence theorems.

## E. Generalized / benchmark theorem surface

`Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremsMonolith.agda` is separate from the canonical theorem source.

It contains generalized theorem infrastructure and the Mercury-named structures:

- `MercuryJaxtarAQCertificate`
- `MercuryJaxtarAQEmergence`

Those names should not be read as ownership of the canonical theorem source.

`GeneralClosedLoopBenchV2.agda` supplies generalized learner benchmark loops, environments, and ablation records.

## F. Verification rule

A theorem is considered verified by repository policy only after its owning Agda module passes the current configured Guix `agda --safe` lane.

A record field is not counted as a separate derived theorem merely because the field name appears inside a certificate record.

The generated semantic artifact is likewise not considered accepted merely because Mercury emitted it.
