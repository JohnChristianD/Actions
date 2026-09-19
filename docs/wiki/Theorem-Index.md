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


### Existing TSTS endogenous connected composition

The TSTS connected theorem remains in the canonical theorem monolith as an existing theorem surface:

- `FiniteTSTSBranch`
- `FiniteTSTSPosterior`
- `finiteTSTSSelect`
- `finiteTSTSSelectedProbe`
- `finiteTSTSSelectedTarget`
- `finiteTSTSReward`
- `finiteTSTSNextPosterior`
- `finiteTSTSClosedStep`
- `FiniteTSTSEndogenousConnectedTheorem`
- `finite-tsts-endogenous-connected-theorem`

It is no longer the search target for theorem discovery. Discovery treats these laws as already included and searches for new learner-local structure around the remaining theorem surface.

### Intrinsic endogenous attention-mediator theorem

The search architecture is deliberately excluded from this theorem. The active learner theorem is:

- `FiniteAttentionWatkinsGRUF4MediatorTheorem`
- `finite-attention-watkins-gru-f4-mediator-theorem`

It proves a structural separation-and-coupling result for arbitrary attention-state replacement:

`attention replacement -> unchanged policy/count/Q-log channels -> endogenous Watkins expression -> shared GRU/F4 consumption`

The theorem also preserves the NormPair observable and persistent-GRU quotient through the canonical full step.

This is independent of TSTS, evolutionary search, program search, PVS, and JAxtar.

A literature check found extensive prior work combining attention with GRU/recurrent RL and prior Q-learning convergence theory, but the exact formal finite-state mediator theorem above was not found in the checked sources. This should therefore be described as a narrow repository-local novelty candidate, not as a definitive literature-priority claim.

## Learner theorem-discovery target

Automated theorem discovery searches for modular identities of the learner itself, including invariances, equivariances, commuting diagrams, quotient-preserving transformations, and related structural laws.

A candidate must act on an actual learner carrier or learner-derived observable, survive the Mercury equivalence quotient, not already be represented in the canonical theorem source, and generate a compositional Agda proof rather than a bare reflexivity proof.

The current raw basis uses:

- NormPair replacement;
- period-4 clock replacement;

crossed with the following observables:

- canonical count step;
- canonical Q-log step;
- canonical endogenous feedback;
- canonical Watkins target.

Each observable also has an iterate candidate in the raw grammar. Mercury quotients those downstream forms into the one-step basis.

The current emitted basis is:

- `candidate_normReplacement_countStep_invariant`;
- `candidate_normReplacement_qLogStep_invariant`;
- `candidate_clockPlus4_endogenousFeedback_invariant`;
- `candidate_clockPlus4_watkinsTarget_invariant`.

The generated proof module is `GeneratedNovelLearnerTheorems.agda`. Passing `agda --safe` is required before any candidate can be considered verified.

## Learner-local symbolic composition algebra

The canonical learner still exports the existing composition laws:

- `LearnerReplacement`
- `applyLearnerReplacement`
- `applyLearnerReplacements`
- `canonicalPolicy-learnerReplacement-invariant`
- `canonicalPolicy-learnerReplacement-composition`
- `canonicalNormPair-afterFullStep-iterate`
- `canonicalPersistentGRU-afterFullStep-iterate`

Those laws are now inputs to novelty pruning rather than the discovery target itself.

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
