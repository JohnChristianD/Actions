# Endogenous Int8 Learner Design

## Goal
Build a real finite Int8 learner whose semantics, exploration kernel, theorem discovery, and extracted executable are all anchored by Agda `--safe`, with false or under-specified conjectures pruned rather than represented by inert certificates.

## Architecture
Agda is the sole mathematical authority. The learner is a finite exact state machine with uniform Int8 parameter representation and explicitly finite/dyadic auxiliary state. Candidate theorem generation is external orchestration only; acceptance is exclusively `agda --safe`. Agda2HS extracts the implemented pure learner for practical execution but is not a second proof authority.

The work is split into three independently testable subsystems: (A) the actual learner and representation/TD algebra, (B) the finite exploration and Markov kernel, and (C) theorem discovery, Agda2HS extraction, and CI gating.

## Mathematical constraints

- No postulates, holes, inert certificates, or unchecked axioms.
- Every retained theorem is a concrete proposition with a concrete `--safe` proof term.
- Parameters use a uniform Int8 representation wherever the learner requires trainable scalar parameters.
- Softsign, signReLU, CReLU, frozen Haar, and projection operators are implemented as real finite functions before theorem claims are made about them.
- Top-k Sparsemax is admitted only with an explicit arithmetic-closure condition; arbitrary support cardinality must not be silently called dyadic.
- Replay redundancy is proved only for the exact prefix-preserving replay relation that makes it mathematically true.
- True Online TD is implemented and checked against a finite forward-view specification; any stronger literature claim is retained only if the instantiated finite theorem closes in `--safe`.
- Aperiodicity, irreducibility, recurrence, invariant-measure, and mixing claims require an explicit finite transition kernel.
- Fixed-window POMDP Markovianization is conditional on a formal finite sufficient-statistic hypothesis.
- CNN equivalence is an exact finite-function equality target, not an informal architectural analogy.

## Canonical exploration policy
The configuration retains exactly one exploration constructor at a time. The implementation must provide at least one explicit finite non-Gaussian distribution. Candidate mechanisms include a finite Noisy-Net-style parameter perturbation, a finite MR15-style population transition, and a finite OpenES-style population transition. No mixed mechanism may be promoted to the canonical configuration.

The canonical choice is selected only after comparing the actual finite transition systems by proof obligations: dyadic closure, self-loop availability, finite support reachability, state-space finiteness, and extraction practicality.

## Acceptance gates

1. All learner modules pass `agda --safe`.
2. Canonical aggregate imports every retained theorem transitively.
3. No theorem is accepted solely because it is definitional configuration equality such as `x ≡ x`.
4. Agda2HS produces compilable Haskell for the actual learner module.
5. The CI workflow rejects retired optimizer traces and any proof bypasses.
6. The discovery loop records only kernel-accepted conjectures and deletes/prunes failed candidate statements.

## Explicit non-goals
No claim is made that Noisy Nets, MR15-GA, or OpenES is universally ergodic in its conventional real-valued form. No claim is made that a finite observation window exactly Markovianizes an arbitrary POMDP. No claim is made that Haar alone produces CNN equivalence or sparsity.
