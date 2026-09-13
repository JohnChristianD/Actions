# Theorem-first finite ERL/EA replication wiki

Authority: Agda `--safe`.

Repository CI checks the canonical source, finite exploration kernels, admissible dyadic laws, the softsign-gated representation, the Noisy-Net representation factor, finite CHAD/Möbius composition modules, and the generated law×method theorem surface.

## Actual exploration methods

Exactly three actual exploration methods are admitted: MR15, OpenES, and Noisy Nets. Probability laws are parameters to those methods, not separate explorers.

## Permanent law pruning

The former triangular law is permanently absent from the selectable theorem surface. The former `DyadicGeometric5` candidate is also permanently pruned because its support is contiguous integer radius rather than a dyadic power-of-two shell family.

The retained exact finite laws are:

- Lazy Walk: weights `2,1,1` over `{0,+1,-1}`, denominator `4`.
- Dyadic Ladder: weight `16` at zero and weight `1` on each signed power-of-two shell through `±128`, denominator `32`.
- Flat Dyadic: uniform weight `1` over all `256` Int8 residues, denominator `256`.

All three are exact dyadic, symmetric, centered at zero, contain zero mass for a one-step self-loop, and contain ±1 support for the additive `Z_256` generator theorem. Lazy Walk is the minimal local-support law; Dyadic Ladder supplies multiscale dyadic shells; Flat Dyadic supplies full support.

Rademacher-only support omits zero and therefore loses the one-step self-loop witness. Even-step laws have nontrivial gcd with `256` and therefore cannot generate the full additive torus. Same-support probability reshapes are theorem-equivalent under the current support-based graph interface and are pruned from the theorem frontier.

## Canonical exploration boundary

The canonical exploration theorem is attached to the softsign-gated representation layer:

`E -> RoPE -> Pyr^top-k -> Fastfood_frozen -> signReLU8 -> softsign8 -> GateNN -> Pi`.

MR15 now uses `SoftsignGatedRepresentation = Int8 × Int8` as its state. OpenES is the scalar `Int8` quotient used as a lower-dimensional ablation and factor target, not the canonical representation boundary.

`Exotic/ERL/FullCoupled/SoftsignGatedRepresentation.agda` contains the representation state and step relation. `Exotic/ERL/FullCoupled/NoisyNetSoftsignFactor.agda` contains the actual Noisy-Net projection, section, retraction, step projection, and step lift.

## CHAD and Möbius composition

`Exotic/efficient_chad/SoftsignGatedComposition.agda` proves the exact CHAD forward and pullback composition for `softsign8 ∘ signReLU8` at the abstract finite operator boundary.

`Exotic/efficient_chad/MobiusInt8Composition.agda` proves closure of finite homogeneous-coordinate actions under composition. This is a genuine finite composition theorem, but it is not an activation-specific Möbius certificate: concrete signReLU8 and softsign8 Möbius witnesses still require concrete in-tree activation semantics and the corresponding projective/denominator theorem.

So the current emergent algebra proves CHAD composition and generic finite Möbius closure; it does not fabricate an activation-specific Möbius identity that is not yet witnessed in-tree.

## Why MR15 and OpenES had identical theorems

The earlier repair encoded both as arbitrary fresh-target relations over finite surrogate states. Their irreducibility and self-loop proofs were therefore isomorphic shells and erased the state-layer distinction.

That abstraction is now separated:

- OpenES state: `Int8`.
- MR15 state: `SoftsignGatedRepresentation = Int8 × Int8`.
- OpenES is the first-coordinate quotient of MR15.
- MR15 has a section `x ↦ (x,0)` back into its representation state.
- The strict witness is `(1,0)` versus `(1,1)`: same OpenES projection, distinct MR15 state.

## Noisy-Net representation factor

`NoisyNetSoftsignFactor.agda` proves a concrete factor from `CoupledNoisyNetState` to the softsign-gated representation, with exact projection, section, retraction, step projection, and step lift. The hidden `sigma3` coordinate supplies a proper fiber, so the full coupled state is a genuine factor-extension of the representation theorem state.

## Strict theorem ordering

The current strict ordering is a factor-theorem ordering, not a statistical ranking:

`OpenES < MR15 < NoisyNet`.

`TheoremStrengthV3.agda` transfers irreducibility, self-loop, and `PeriodOne` through certified projection/section factors. Proper-fiber witnesses distinguish the state classes. Thus Noisy Nets is the strongest connected state-level theorem class presently represented in-tree, with no statistical quantity entering the ordering.

The law axis is a support-based partial order:

`LazyWalk ⊂ DyadicLadder ⊂ FlatDyadic`

where the inclusion refers to positive support once a law is instantiated into the actual transition kernel. The present `FullAlgebraicCoupling` already records exact law normalization/unit support together with the method theorem, but a genuinely law-dependent graph-strength theorem still requires the next algebraic step: `instantiate(method, law)` must construct the transition relation consumed by irreducibility and period proofs.

## Full emergent theorem surface

For every retained permutation, the generated object has the shape `FullAlgebraicCoupling law step`. Its fields combine exact law normalization, unit-generator support, signReLU8-to-softsign8 CHAD forward/pullback composition, method irreducibility, actual self-loop, and derived `PeriodOne`.

The current nine permutations are:

- Lazy Walk × OpenES: scalar quotient full-coupling theorem.
- Lazy Walk × MR15: softsign-gated representation full-coupling theorem.
- Lazy Walk × Noisy Nets: full learner theorem plus Noisy-Net-to-representation factor.
- Dyadic Ladder × OpenES: scalar quotient full-coupling theorem with ladder support.
- Dyadic Ladder × MR15: softsign-gated representation full-coupling theorem with ladder support.
- Dyadic Ladder × Noisy Nets: full learner theorem plus factor and ladder support.
- Flat Dyadic × OpenES: scalar quotient full-coupling theorem with full Int8 support.
- Flat Dyadic × MR15: softsign-gated representation full-coupling theorem with full Int8 support.
- Flat Dyadic × Noisy Nets: full learner theorem plus Noisy-Net factor and full Int8 support.

These are theorem objects assembled only after the finite algebraic components are available; Haskell merely emits source and invokes `agda --safe`.

## Automated validation

The last completed canonical run before the factor refactor passed the permanent scope guard, canonical source, and canonical regression, then failed at the MR15 proof gate; later checks were skipped. The representation primitive gate passed on that same head. The latest refactor adds the separated Noisy-Net factor, Flat Dyadic, removal of the geometric-5 law, and the updated generator/workflow, so a fresh current-head run is required before calling the branch green.

The active theorem carrier is finite Int8 and all local probability/algebra facts are exact constructors. CI timing is the validation authority, but speed is not used to define theorem strength.

## Replication order

Keep methods and laws separate. Explore at the softsign-gated representation boundary. Instantiate every retained law into every actual method. Compose the resulting transition with the full algebraic learner/representation theorem. Require concrete projection/lift theorems before strict method comparison. Treat Möbius closure as generic until activation-specific witnesses are actually proven. Let Agda `--safe` remain the final authority.
