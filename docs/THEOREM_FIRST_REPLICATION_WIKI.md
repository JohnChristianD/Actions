# Theorem-first finite ERL/EA replication wiki

Authority: Agda `--safe`.

Repository CI checks the canonical source, finite exploration kernels, the retained exact dyadic law frontier, the softsign-gated representation, the Noisy-Net representation factor, finite CHAD/Möbius composition modules, and the generated method×law theorem surface.

## Actual exploration methods

MR15 and OpenES are the actual representation-level exploration ablations. Noisy Nets is a coupled learner/noise ablation inside the full learner state, not a detached explorer. Probability laws are parameters to the exploration boundary.

## Permanent law pruning

The obsolete triangular family, the geometric-5 candidate, Lazy Walk, and every present law outside the retained flat or shell-structured dyadic frontier are permanently absent from the selectable theorem surface.

The retained exact law frontier has two members:

- Flat Dyadic: uniform weight `1` over all `256` Int8 residues, denominator `256`. It is exact dyadic, symmetric, constant-profile unimodal, aperiodic through positive zero mass, and irreducible at the additive `Z_256` support level because ±1 are present. It is the flat baseline; it is not an exact scale-shell law.
- Dyadic Ladder: denominator `32`, stay weight `16`, and weight `1` on each signed shell `±1, ±2, …, ±128`. It is exact dyadic, symmetric, unimodal, aperiodic, irreducible, and internally shell-structured across the available finite powers of two. The ±1 shell supplies the generator witness, while the full ladder preserves all available dyadic scales as support.

The ladder is the natural exact finite candidate for the requested shell-scaling property. A globally scale-invariant finite law needs an explicit boundary convention because repeated doubling eventually reaches the Int8 boundary. The kernel-friendly formulation is therefore finite shell covariance together with exact closure.

## Canonical exploration boundary

Exploration is attached algebraically to the softsign-gated representation layer:

`E -> RoPE -> Pyr^top-k -> Fastfood_frozen -> signReLU8 -> softsign8 -> GateNN -> Pi`.

`SoftsignGatedRepresentation = Int8 × Int8` is the canonical representation theorem carrier. MR15 uses that full carrier. OpenES is the first-coordinate `Int8` quotient and is intentionally a lower-dimensional factor theorem. Noisy Nets projects to the same softsign-gated representation and admits an explicit section/retraction, so the coupled learner theorem strictly extends the representation theorem by a proper fiber.

## CHAD and Möbius composition

`Exotic/efficient_chad/SoftsignGatedComposition.agda` proves the exact CHAD forward and pullback composition for `softsign8 ∘ signReLU8` at the finite operator boundary.

`Exotic/efficient_chad/MobiusInt8Composition.agda` proves finite homogeneous-coordinate action closure under composition.

`Exotic/efficient_chad/MobiusSoftsignBridge.agda` proves the actual emergent composition theorem: once concrete forward Möbius witnesses exist for signReLU8 and softsign8, the composed `softsign8 ∘ signReLU8` operator receives a derived Möbius witness. The full algebraic coupling record now carries that closure theorem. The repository still does not fabricate the missing activation-specific witnesses.

## Why MR15 and OpenES are not the same theorem

The old unrestricted fresh-target shells made them look identical. That abstraction has now been split by carrier.

- OpenES state is `Int8`.
- MR15 state is `SoftsignGatedRepresentation = Int8 × Int8`.
- OpenES is the first-coordinate quotient of MR15.
- MR15 has a section `x ↦ (x,0)`.
- `(1,0)` and `(1,1)` have equal OpenES projection but are distinct MR15 states.

Therefore OpenES and MR15 share the same graph-theorem shape (`Irreducible`, `SelfLoop`, `PeriodOne`) but are not logically equivalent theorem classes. MR15 strictly refines the state theorem through a proper factor extension.

## Noisy-Net representation factor

`NoisyNetSoftsignFactor.agda` is the concrete bridge from the whole coupled Noisy-Net state to the softsign-gated representation. It proves projection, lift, retraction, step projection, and step lift. The coupled gate-parameter fiber supplies the strictness witness. `TheoremStrengthV3.agda` composes that factor with the MR15→OpenES factor.

## Strict theorem ordering

The current semantic theorem order, ignoring statistics, is:

`OpenES < MR15 < NoisyNet`.

This is a real factor-extension ordering. It is not a count of witnesses: each `<` is backed by a projection/lift theorem plus an explicit proper-fiber witness, and the composite NoisyNet→OpenES factor is derived in Agda.

The law dimension is orthogonal: Flat Dyadic and Dyadic Ladder are alternative exact probability laws. At the present abstraction, they do not change the graph relation itself, so they must not be ranked as stronger graph theorems merely from normalization/support facts. Their theorem-bearing difference is algebraic law structure: Flat gives uniform one-step target universality; Ladder gives explicit finite shell structure across dyadic scales.

## Full emergent theorem surface

The generator now emits six endogenous full-composition objects:

`OpenES × Flat`, `OpenES × DyadicLadder`, `MR15 × Flat`, `MR15 × DyadicLadder`, `NoisyNet × Flat`, and `NoisyNet × DyadicLadder`.

Each object contains exact law normalization and ±1 support, the signReLU8→softsign8 CHAD forward/pullback composition, the conditional Möbius forward-closure theorem, the canonical softsign-gated `PeriodOne`, and the method/coupled-state irreducibility and self-loop facts that Agda actually proves.

The current graph kernels are still theorem abstractions over their production stochastic semantics. The next strict boundary is law-dependent transition instantiation: the selected law must become the actual finite support used by the representation transition, not merely an attached normalization witness. That is the only point at which law choice can change the graph theorem itself.

## Automated validation

The canonical workflow now checks the retained Flat Dyadic and Dyadic Ladder modules, the full algebraic coupling record, CHAD/Möbius composition, the softsign representation factor, the strict theorem ordering, and the generated six-permutation report under `agda --safe`.

CI runtime is validation plumbing. It is not a statistical performance measurement.

## Current mathematical answer on candidate laws

Flat Dyadic is eligible for symmetry, unimodality, aperiodicity, irreducibility, and exact dyadic closure, but not for exact global scale-shell invariance. Dyadic Ladder is the stronger structural candidate for the requested scale property because its positive support is organized by signed powers of two with equal shell mass and positive zero/±1 mass.

The most economical future addition is not another arbitrary distribution family. If a new law is admitted, it should be a finite dyadic-shell construction with exact power-of-two weights, explicit boundary behavior, positive zero mass, positive ±1 mass, symmetry, and a kernel-checked finite shell-scaling theorem. Continuous or unrelated candidate families do not belong in the retained frontier.

No data analysis or empirical ranking is used anywhere in these conclusions.
