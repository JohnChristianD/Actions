# Learner equivalence class: algebraic and computational boundary

## Question

Classify the canonical learner by its proved mathematical properties rather than by definitional refl structure.

## Verified facts

The canonical full transition is a deterministic endomorphism on CanonicalFullLearnerState. Its state contains finite local GRU/Watkins/F4/L2/control components, a Nat-indexed action domain, Nat LCB counts whose total increases by exactly one per full step, and a finite-rational q-log value. No dedicated clock coordinate is part of the state.

The formal consequences include exact iterate growth, aperiodicity, and exclusion of every nontrivial finite cycle. These are semantic transition properties, not merely definitional identities.

The recurrent input layer has an exact prefix-monoid action: finite input words map to state endomorphisms, with append corresponding to composition in the opposite endomorphism convention.

The new RecurrentScanConjugacyTheorem strengthens that scan algebra: if a replacement map commutes with one local transition, the equality lifts to every recurrent prefix. This is a closure theorem over the scan semantics.

## Equivalence-class characterization

The most precise current description is: a deterministic, discrete-time, counter-augmented recurrent transition system with finite local neural/control carriers, finite action/output alphabets, monotone unbounded counters, and an exact recurrent prefix monoid action.

This is more precise than calling it a Transformer, S4, S5, or generic RNN. It is not equivalent to a finite-state machine because the full state is infinite through Nat clock/count components. It is also not established as a Turing-complete machine.

## Turing-completeness boundary

The repository proves that ExactNatObservationSimulation and ExactTuringCounterObservation are impossible when the observation codomain is Int8. This is an exact finite-observation boundary.

That result does not by itself prove that the entire learner is non-Turing-complete. The overall state is infinite because of Nat components, so finite local carriers alone are not enough to establish Turing incompleteness.

Conversely, unbounded counters do not establish Turing completeness. The current formalization does not provide a universal-machine simulation, writable unbounded tape, or a proved encoding/decoding of arbitrary Turing-machine configurations.

The strongest defensible statement at the current proof surface is: the learner has an infinite-state, deterministic counter-augmented recurrent semantics, but no exact Turing-complete equivalence has been established; moreover, exact injection of an unbounded Nat counter through a single Int8 observation is formally impossible.

## New endogenous theorem

canonical-recurrent-scan-conjugacy-theorem is the new endogenous theorem. It is generated from the existing local transition law plus the existing recurrent-prefix semantics; it introduces no new proof axiom.

Informally: replace composed with step equals step composed with replace implies replace composed with Prefix(xs,n) equals Prefix(xs,n) composed with replace.

## Scope boundary

This classification is a semantic equivalence-class description of the current Agda model. It is not a claim that every externally implemented model with similar informal components belongs to the same class. Transfer requires an explicit representation map and proof of the relevant transition, observation, and scan laws.

## Primary sources

- Pérez, Marinković, and Barceló, On the Turing Completeness of Modern Neural Network Architectures: https://arxiv.org/abs/1901.03429
- Carmantini et al., Turing Computation with Recurrent Artificial Neural Networks: https://arxiv.org/abs/1511.01427

## Scan-wide connected coupling

The graph now has an explicit bridge from local full-learner transition conjugacy to arbitrary `iterateCanonical` depth, plus the existing GRU/F4/Norm projection bridge. This closes the ambiguity between a local commuting law and a whole-learner scan law: the latter is an induction over the actual full transition. The theorem does not claim Turing completeness or incompleteness; it only transports an explicitly supplied conjugacy witness across the learner's deterministic scan.

## Turing-completeness ambiguity pruning

The literature distinguishes computational universality claims by their resource assumptions. Pérez et al. prove Turing completeness for particular Transformer/Neural-GPU constructions under their stated assumptions; Carmantini et al. give constructive recurrent-network simulations; finite-precision RNN work emphasizes that precision and computation-time assumptions materially change the result. Therefore this repository should not infer universality or non-universality from the architecture label alone. Its formal negative result is narrower: exact unbounded-Nat counter recovery through finite `Int8` observation is impossible. The current model remains an infinite-state deterministic system because of its `Nat` components, so a full Turing-completeness classification requires a separate machine-simulation witness or impossibility theorem.

## Dedicated novelty review: scan conjugacy and exact coupling

### What is and is not implied

The repository has two distinct scan semantics.

1. The autonomous full transition is canonicalFullStep K : CanonicalFullLearnerState → CanonicalFullLearnerState, and iterateCanonical K n is its n-fold power. A commuting square for canonicalFullStep K therefore lifts to every time iterate by induction.

2. The recurrent-prefix scan is recurrentPrefixState R xs n, where the transition depends on the input element xs n. A theorem about powers of one autonomous time operator does not imply arbitrary input-word prefix conjugacy, because these are different operators. Exact prefix conjugacy instead needs the per-input commuting law and the existing recurrentPrefix-scan-lifts-conjugacy.

So the new full-learner scan theorem is a time-iteration closure theorem, not a silent replacement for the input-prefix theorem.

### Novelty review

The abstract mathematical ingredients are not new. Commuting maps, centralizers, conjugacies, and equivariance are established concepts; recent dynamical-systems work still studies centralizers as maps commuting with fixed dynamics, and recent sequence-model work explicitly studies equivariance of recurrent networks and notes that standard RNNs are generally not flow-equivariant.

The potentially distinctive repository contribution is narrower: an Agda-checked theorem surface that combines the exact discrete Int8 learner, its nested full state, the exact recurrent prefix algebra, the autonomous full transition, explicit modified-Watkins coupling, and scan-wide conjugacy. A targeted primary-source search found no directly matching theorem for this exact composition, precision, and coupling, but this is not exhaustive prior-art clearance.

The strongest defensible novelty wording is therefore: new endogenous theorem/combination in the formalized model, not a claim of a first-ever recurrent conjugacy class.

### Full Watkins coupling boundary

The earlier CanonicalFullLearnerConnectedScanConjugacyTheorem projected only the GRU/F4/Norm network. Watkins was present inside canonicalFullStep, but the connected witness did not explicitly expose the Watkins state or the target flow.

The theorem is now repaired to expose four exact Watkins-coupling facts: full-step Watkins projection equals canonicalWatkinsStep; canonicalSignal equals the exact modified Watkins target; the same target is consumed by the GRU step; and the same target is consumed by the F4/L2 optimizer step. This makes the coupling explicit without introducing a second learner semantics.

### Exact Turing-completeness boundary

The previously proposed CanonicalExactCompositionTuringCompletenessTheorem was too strong and, for the current exact composition, internally inconsistent. Its universal step-simulation field quantifies over arbitrary exact two-counter machines.

A self-looping two-counter machine then requires encode c = canonicalFullStep (compile M) (encode c), while the exact learner proves canonicalFullStep K s ≢ s for every K,s because the Nat clock increments exactly once per step.

The positive universal contract therefore cannot be inhabited for this exact transition system. The formal surface has been repaired into an explicit contract plus an Agda proof that the contract is impossible. That is a stronger exact result than leaving a fake positive universality theorem as an unproven record type.

This does not by itself prove that every conceivable notion of computational universality is impossible for every encoding convention. It proves that this specific exact one-step, state-equality simulation contract cannot hold.

## Primary-source novelty references

- Keller, Flow Equivariant Recurrent Neural Networks (2025): https://arxiv.org/abs/2507.14793
- Weiss, Goldberg, Yahav, On the Practical Computational Power of Finite Precision RNNs for Language Recognition (2018): https://arxiv.org/abs/1805.04908
- Pérez, Marinković, Barceló, On the Turing Completeness of Modern Neural Network Architectures (2019): https://arxiv.org/abs/1901.03429
- Bonomo, Rocha, Varandas, Discrete symmetries of smooth flows and their time-t maps (2024): https://doi.org/10.1016/j.jmaa.2024.128534