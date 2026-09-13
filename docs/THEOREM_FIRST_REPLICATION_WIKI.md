# Theorem-first finite ERL/EA replication wiki

Authority: Agda `--safe`.

Repository CI checks the canonical source, finite exploration kernels, the single retained exact dyadic law, the softsign-gated representation, the Noisy-Net representation factor, finite CHAD/Möbius composition modules, and the generated method theorem surface.

## Actual exploration methods

Exactly three actual exploration methods are admitted: MR15, OpenES, and Noisy Nets. Probability laws are parameters to those methods, not separate explorers.

## Permanent law pruning

The former triangular law and `DyadicGeometric5` candidate are permanently absent from the selectable theorem surface. All currently implemented non-flat dyadic probability laws have also been removed from the active theorem surface; Flat Dyadic is now the sole retained law.

The retained exact finite law is Flat Dyadic: uniform weight `1` over all `256` Int8 residues, denominator `256`. It is exactly dyadic, symmetric under group negation, centered, weakly unimodal as a constant profile, contains zero mass for a one-step self-loop, and contains ±1 support for the additive `Z_256` generator theorem.

A future scale-self-similar candidate can be built from dyadic shells with exact power-of-two weight ratios while preserving zero and ±1 support. It is not admitted until its normalization, symmetry, unimodality, scale law, and actual transition instantiation are kernel-checked.

## Canonical exploration boundary

The canonical exploration theorem is attached to the softsign-gated representation layer:

`E -> RoPE -> Pyr^top-k -> Fastfood_frozen -> signReLU8 -> softsign8 -> GateNN -> Pi`.

MR15 now uses `SoftsignGatedRepresentation = Int8 × Int8` as its state. OpenES is the scalar `Int8` quotient used as a lower-dimensional ablation and factor target, not the canonical representation boundary.

`Exotic/ERL/FullCoupled/SoftsignGatedRepresentation.agda` contains the representation state, step relation, irreducibility, self-loop, and `PeriodOne`. `Exotic/ERL/FullCoupled/NoisyNetSoftsignFactor.agda` contains the actual Noisy-Net projection, section, retraction, step projection, and step lift.

## CHAD and Möbius composition

`Exotic/efficient_chad/SoftsignGatedComposition.agda` proves the exact CHAD forward and pullback composition for `softsign8 ∘ signReLU8` at the abstract finite operator boundary.

`Exotic/efficient_chad/MobiusInt8Composition.agda` proves closure of finite homogeneous-coordinate actions under composition.

`Exotic/efficient_chad/MobiusSoftsignBridge.agda` now proves the conditional activation theorem: given concrete forward Möbius witnesses for signReLU8 and softsign8, their composition has a concrete forward Möbius witness for the softsign-gated operator. The bridge does not fabricate either activation witness.

External finite-field Möbius literature is contextual only; Agda remains the theorem authority.

## Why MR15 and OpenES are not the same theorem class

Their early surrogate kernels looked identical because both used unrestricted fresh-target relations. That made their bare `Irreducible × SelfLoop × PeriodOne` packages isomorphic.

The state-aware theorem surface now separates them:

- OpenES state: `Int8`.
- MR15 state: `SoftsignGatedRepresentation = Int8 × Int8`.
- OpenES is the first-coordinate quotient of MR15.
- MR15 has a section `x ↦ (x,0)` back into its representation state.
- The strict separator is `(1,0)` versus `(1,1)`: equal quotient image, distinct representation states.

Thus their raw period theorem is the same shape, but their theorem interfaces are not the same: MR15 strictly refines the state carrier by a proper factor extension.

## Noisy-Net representation factor

`NoisyNetSoftsignFactor.agda` proves a concrete factor from `CoupledNoisyNetState` to the softsign-gated representation, with exact projection, section, retraction, step projection, and step lift. The coupled `sigma3` coordinate supplies a proper fiber, so the full learner state is a genuine strict extension of the representation theorem state.

## Strict theorem ordering

The current strict ordering is a semantic factor-extension ordering, not a witness-count or statistical ranking:

`OpenES < MR15 < NoisyNet`.

The order is read as: there is a certified projection/section factor from the stronger state theorem to the weaker theorem, the weaker theorem is recovered by factor transfer, and the stronger carrier has an explicit proper fiber. Therefore the chain is genuinely strict at the state-theorem boundary.

`TheoremStrengthV3.agda` proves the transfer of irreducibility, self-loop, and `PeriodOne` through these factors. `NoisyNetSoftsignFactor.agda` is the concrete bridge that makes the Noisy-Net step strictly connected to the softsign-gated representation.

Ignoring statistics, Noisy Nets is therefore the strongest theorem class currently represented in-tree, MR15 is strictly intermediate, and OpenES is the scalar quotient endpoint. This is a structural theorem order only.

## Full emergent theorem surface

The generator now emits exactly three endogenous objects, one for each actual method with Flat Dyadic:

- Flat Dyadic × OpenES: scalar quotient full algebraic coupling theorem.
- Flat Dyadic × MR15: canonical softsign-gated representation full algebraic coupling theorem.
- Flat Dyadic × Noisy Nets: full coupled learner theorem, plus the certified Noisy-Net-to-softsign representation factor.

Every generated object has exact law normalization, unit-generator support, signReLU8-to-softsign8 CHAD forward/pullback composition, the canonical softsign representation `PeriodOne`, method irreducibility, actual self-loop, and derived method `PeriodOne`.

The remaining proof boundary for a genuinely law-dependent graph theorem is explicit: `instantiate(method, law)` must construct the actual transition relation consumed by the reachability proof. Until then, the law contributes exact probability algebra, while the graph theorem comes from the concrete method relation.

## Automated validation

The previous canonical run on the refactor head passed the permanent scope guard and canonical source/regression, then failed at the MR15 gate because `SoftsignGatedComposition.agda` lacked the equality import for `≡`. That source defect has been repaired. A fresh current-head run is required before calling the branch green.

The active theorem carrier is finite Int8 and all local probability/algebra facts are exact constructors. CI time is validation plumbing, not theorem strength; no empirical performance claim is inferred.

## Replication order

Keep methods and laws separate. Explore at the softsign-gated representation boundary. Retain only Flat Dyadic in the active law frontier. Compose the resulting transition with the full algebraic learner/representation theorem. Require concrete projection/lift theorems before strict method comparison. Treat Möbius closure as conditional on concrete activation witnesses. Let Agda `--safe` remain the final authority.
