# Theorem Index

## A. Kernel-checked canonical results

### `F4HardsignKernel.agda`

`clip-add-boundary`: canonical clipping at +127.

`scaled-mul-example`: scaled signed multiplication gives 32 for 64 and 64.

`identity-gate-example`: a positive Int8 input maps to the positive hard-sign gate.

`mobius-gate-example` and `mobius-singularity`: the optional Möbius branch machinery has the expected finite-rational cases.

`state-independent-gate`: the identity gate ignores any state arguments.

### `CanonicalCoupledF4Learner.agda`

`canonicalSign-state-independent`: canonical sign gate is a function of the input alone.

`canonicalF4-global-L2-law`: the code-level definition of the coupled parameter-level βθ term reduces definitionally to the stated Δθ expression.

`canonicalF4-old-ell-law`: the power-of-two factor uses the pre-update level.

`canonicalCoupledStep-clock`: one coupled step increments the clock.

`canonicalCoupledGRU-gate-law`: the canonical gate remains the sign function in the coupled learner.

### `CanonicalCoupledCompositionTheorems.agda`

`canonicalCoupled-step-clock`: inherited clock law.

`canonicalCoupled-no-fixed-point`: the coupled step cannot be a fixed point because the clock strictly increments.

`reservoir-condition`: a left inverse implies injectivity and therefore discrete separation of distinct states.

`canonical-reservoir-condition`: the identity observation is a concrete lossless witness, so its NSP-style separation is closed.

`signGRUScan-depth-unbounded`: natural-number scan depth is not bounded by any finite predecessor B.

`associative-scan-triple`: triple composition of the scan action is propositionally equal in both parenthesizations.

`simultaneous-coupled-closure`: packages the reservoir-separation, arbitrary-depth-index, and triple-associativity results into one record.

Important: the reservoir result here is an exact left-inverse/identity observation theorem. It does not establish that an arbitrary learned reservoir observation is injective.

## B. General reservoir and attractor results

`finiteCore-collision` and `finiteCore-tail-repeat` derive eventual repetition for any `Int8 -> Int8` deterministic map from finite-state pigeonhole reasoning.

`hiddenProjection-step` and `hiddenProjection-step`'s law expose the hidden-state projection of the general learner step.

`l1Weight-step-monotone` and `l1Weight-is-progress-not-dissipation` prove monotonic accumulation of the norm counter. They do not prove Lyapunov descent.

`basin-by-energy` derives a basin hit from the supplied `SymmetricAssociativeReservoir` fields, especially strict energy decrease outside the attractor.

`invariant-after-hit` proves that an already-hit attractor remains invariant under the supplied invariant field.

`contextualRecall` derives a cue-specific basin hit from a supplied `MultiAttractorReservoir` certificate.

`contextualRecall-disjoint` is exactly the disjointness field exported by that certificate.

These are conditional theorems over records whose dynamics, invariant sets, energy, and descent properties are supplied as fields.

## C. General theorem monolith

The general theorem monolith contains reusable algebraic and proof-packaging infrastructure, including:

`learnerStep-clock`, `learnerNoFixedPoint`, `iterateLearner-clock`, and `clock-lower-bound` for the clocked learner.

`gruPersistentLaw`, `gruStep-respects-equivalence`, and Möbius composition/prefix laws.

finite piecewise-rational closure through `prBranch-closure`, `prComposeInput-closure`, `prIterated-closure`, and `unbounded-depth-piecewise-rational-closure`.

`finiteStateParameterComplete` for a fully typed finite-state kernel record.

ordered-carrier and midpoint machinery uses collision-safe field names `carrier≤` and `midpoint≤`.

The theorem monolith also contains certificate records such as `LyapunovCertificate`, `ObservabilityWitness`, and related abstraction records. Their presence is not itself a proof that the canonical learner satisfies the fields.

## D. Composite theorem packaging

`MonolithCompositeReservoirTheorem.agda` proves concrete structural facts of the legacy learner, including clock-based non-fixed-point behavior, monotone norm counters, persistent GRU coordinates, and preservation of the legacy `l2Global` field.

`composeMonolith` combines supplied KKT, Lyapunov, attractor, and reservoir certificates into one `CertifiedCompositeConclusion`.

That constructor is a certificate composition theorem. It does not manufacture the KKT proof, strict Lyapunov decrease, attractor basin hit, or reservoir injectivity from the learner dynamics.

In particular, the field `f4Coupling` in this composite module refers to the legacy `L.f4Step` and its stored `l2Global`. It should not be confused with the canonical parameter-level βθ term.

## E. What is not currently established

The current Safe Agda closure does not establish a theorem that the canonical learned reservoir has a nontrivial injective observation map.

It does not establish global Lyapunov descent for the actual canonical coupled learner.

It does not establish a KKT optimum for the sparsemax construction merely because a `KKTPathCertificate` record exists.

It does not establish a global attractor basin for the canonical learner without supplying the corresponding attractor certificate fields.

It does not turn the piecewise-rational theorem representation into the canonical GRU activation.