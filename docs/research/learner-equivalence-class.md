# Learner equivalence class: algebraic and computational boundary

## Question

Classify the canonical learner by its proved mathematical properties rather than by definitional refl structure.

## Verified facts

The canonical full transition is a deterministic endomorphism on CanonicalFullLearnerState. Its state contains an unbounded Nat clock; finite Int8 GRU/Watkins/F4/L2/control components; a finite action space of 64 actions; Nat LCB counts whose total increases by exactly one per full step; and a finite-rational q-log value.

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