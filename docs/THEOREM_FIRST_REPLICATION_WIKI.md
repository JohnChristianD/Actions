# Theorem-first finite ERL/EA replication wiki

Authority: Agda `--safe`.

Repository CI authority: `.github/workflows/agda.yml`, which reads `.ci/canonical-module.txt` and checks both listed files with `agda --safe`.

## Permanent finite theorem scope

The repository is finite, dyadic, and Int8-oriented. The CI gate rejects non-finite analytic families and the pruned legacy triangular distribution family before any Agda proof gate runs. The prohibition is structural: a rejected family returning in source, documentation, generated candidates, or metadata fails CI.

No external theorem family may be imported as a proof shortcut. External references may be audited, but no external source enlarges the accepted Agda theorem surface without a repository-local `--safe` proof.

## Canonical architecture

Intended canonical configuration:

- optimizer: `standardTDLambdaInt8`
- explorer: `modifiedDyadicMR15GA`
- precision: 8 bits
- context window power: 4
- frozen Haar feature
- local attention scale
- mutation target: independent finite dyadic draws per tick
- exact dyadic histogram fitness with exact sorting and rank consistency

The proof authority is the exact Agda definitions present in-tree and checked by `agda --safe`.

## Actual exploration methods

The live actual exploration methods are exactly:

1. MR15: `Exotic/ERL/Exploration/MR15Reachability.agda`
2. OpenES: `Exotic/ERL/Exploration/OpenESDyadic.agda`
3. Noisy Nets: `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda`

Noisy Nets belongs inside the coupled learner state rather than acting as a detached probability module.

The generic graph theorem layer is `Exotic/ERL/Exploration/ExplorationTheoremSchema.agda`.

## Probability-law layer

Lazy Walk, Dyadic Ladder, and Flat Dyadic are probability-law modules, not additional exploration methods.

`Exotic/ERL/Exploration/LazyWalkDyadic.agda` defines a finite common-denominator-4 law with exact stay/forward/backward masses and proves normalization plus positive zero/unit support.

`Exotic/ERL/Exploration/DyadicLadder.agda` defines a finite common-denominator-32 law with a stay mass and signed power-of-two outcomes and proves normalization plus positive unit and power-of-two support.

`Exotic/ERL/Exploration/FlatDyadic.agda` defines the uniform finite law over all 256 Int8 codes with exact denominator 256 and positive zero/unit and extended power-of-two support.

`Exotic/ERL/Exploration/DyadicLaw.agda` is the law interface. It exposes exactly these three accepted finite laws to the composition generator.

## Endogenous law × method theorem class

The theorem frontier is the Cartesian product

`{MR15, OpenES, NoisyNet} × {LazyWalk, DyadicLadder, FlatDyadic}`.

A law is not promoted to a theorem on its own. The theorem object exists only at the full algebraic coupling boundary:

`law + actual explorer + representation boundary + irreducibility + self-loop -> PeriodOne`.

`Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda` carries the exact law-normalization/support proof together with the representation-layer CHAD laws and the actual explorer reachability/self-loop proof, then derives `PeriodOne` through `periodOne-from-components`.

The Haskell discovery generator enumerates all nine permutations and writes them into `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`. Haskell constructs source only; Agda `--safe` decides acceptance.

The nine generated theorem objects are:

- `MR15LazyWalkEndogenous`
- `MR15DyadicLadderEndogenous`
- `MR15FlatDyadicEndogenous`
- `OpenESLazyWalkEndogenous`
- `OpenESDyadicLadderEndogenous`
- `OpenESFlatDyadicEndogenous`
- `NoisyNetLazyWalkEndogenous`
- `NoisyNetDyadicLadderEndogenous`
- `NoisyNetFlatDyadicEndogenous`

No standalone law `PeriodOne` theorem is generated.

## Strict theorem ordering

The ordering is algebraic, not statistical.

First, the finite probability laws admit a strict support-capacity chain. Their exact finite outcome cardinalities are 3 for Lazy Walk, 17 for Dyadic Ladder, and 256 for Flat Dyadic. Thus the one-step finite-support theorem class is strictly ordered:

`LazyWalk < DyadicLadder < FlatDyadic`.

The strictness is witnessed algebraically by the additional exact support facts: Dyadic Ladder adds signed power-of-two moves beyond ±1, while Flat Dyadic covers the entire 256-code Int8 space.

Second, the Noisy-Net method has a genuine strict state-extension theorem over the softsign-gated representation quotient in `Exotic/ERL/FullCoupled/NoisyNetRepresentationProjection.agda`. The projection keeps the pre-softsign Int8 signal, has a section back into the coupled state, and forgets GateParams. Two coupled states with distinct gate parameters project to the same representation signal, while the gate parameters are independently reachable in the coupled fresh-target transition.

Therefore:

`softsign-gated representation < NoisyNet coupled state`.

This is a state-extension theorem, not a comparison of witness-record sizes.

Combining the two proven strict axes gives the unique maximal corner among variants whose representation boundary is currently connected by an actual projection/lift proof:

`NoisyNet × FlatDyadic`.

MR15 and OpenES already have finite irreducibility/self-loop abstractions, but they do not yet have the corresponding production-state projection/lift into this softsign-gated boundary. Hence a strict theorem comparison of MR15 or OpenES against NoisyNet would currently overclaim. They remain incomparable until their own representation-lift theorems are checked by `agda --safe`.

## Full-state theorem discipline

For a transition relation `_—→_`:

`Irreducible = ∀ s t → Reach _—→_ s t`.

`SelfLoop = ∀ s → s —→ s`.

The reusable sufficient package is `Irreducible × SelfLoop -> PeriodOne`.

This is deliberately a full-state statement. Exploration-only reachability does not substitute for learner+EA reachability. The current MR15 and OpenES modules remain explicit finite kernel abstractions until their production mutation/selection transitions are connected. Noisy Nets is already represented on the coupled learner state.

## Representation-layer exploration boundary

The exploration theorem is attached to the representation boundary, not to an unrelated outer state. The intended forward composition is:

`E -> RoPE -> Pyr^top-k -> Fastfood_frozen -> signReLU8 -> softsign8 -> GateNN -> Pi`.

`Exotic/ERL/Finite/Activation.agda` now supplies the concrete finite Int8 `signReLUQ8` and `softsignQ8` forward definitions. `Exotic/ERL/FullCoupled/NoisyNetRepresentationProjection.agda` connects the coupled Noisy-Net state to the softsign-gated representation signal by an actual projection/section and derives the strict hidden-gate extension theorem.

`Exotic/efficient_chad/SoftsignGatedComposition.agda` is the finite CHAD boundary for `softsign8 ∘ signReLU8`. The generic composition law is kernel-checked. A concrete activation-specific Möbius theorem still requires concrete Möbius witnesses for these Int8 forward operators; the composition theorem does not fabricate those witnesses.

## Mutation and finite probability

For an additive coordinate over `Z_256`, the generator target is `gcd(256,S) = 1` for the effective positive-probability increment support `S`.

A one-step self-loop requires effective support containing `0` with positive mass.

Fresh finite noise per tick is the theorem-friendly mutation model because it preserves explicit support witnesses and finite product constructions.

## CHAD and activation composition

CHAD proves the correctness of a differential/VJP interface for a defined computation. Normalization, support, irreducibility, communicating classes, and period remain separate finite-state theorems.

The repository has an exact `CHADOperator` composition theorem in `Exotic/efficient_chad/Int8.agda`. It composes finite operators in the intended order:

`signReLU8 -> softsign8 -> GateNN -> Pi`.

The `softsign8 ∘ signReLU8` forward composition has its own kernel-checked boundary. An activation-specific Möbius result is generated only when concrete in-tree Int8 activation definitions supply the corresponding Möbius laws; the generic CHAD composition theorem does not fabricate that witness.

## External Efficient-CHAD boundary

CI audits Tom Smeding's upstream source in a clean `.ci/external/efficient-chad-agda` checkout and probes the existing proof under the installed Agda toolchain. No new package or project-local Agda library is added by this audit. The upstream file and its own checked-in dependencies remain outside the repository theorem authority.

## Gating-layer counterfactual

`GatingLayerCounterfactual.agda` proves that gate reachability can lift through an explicit full-state lift, while gate-only exploration is insufficient for global full-state irreducibility when a distinct non-gating factor is preserved. Therefore whole-state communication must be proved on the actual coupled transition.

## Fitness theorem

The finite VEB-RL-style `-TD` fitness surface uses exact dyadic histogram masses, exact normalization, ordinal/rank ordering, and exact sorting whenever rank consistency is part of the theorem.

## Why the Int8 theorem loop is fast

The finite Int8 surface is computationally small: the primary code space has 256 values, the law numerators are small exact naturals, and many normalization/composition identities reduce by definitional equality. That makes the finite algebraic kernel checks fast once the dependency graph is warmed. The expensive-looking part is usually library loading or broad dependency checking, not the finite theorem itself. The target remains proof speed from finite exact reduction, not an empirical performance claim.

## Replication order

1. Keep pure DMCP artifacts deleted.
2. Enforce the permanent finite/dyadic theorem-scope exclusions.
3. Keep Lazy Walk, Dyadic Ladder, and Flat Dyadic as exact probability-law modules only.
4. Keep MR15, OpenES, and Noisy Nets as the actual explorer set.
5. Generate every law × method permutation through the full algebraic coupling and representation boundary.
6. Require concrete Agda `--safe` proof terms for every generated theorem object.
7. Connect each finite kernel to its production transition semantics before upgrading theorem status.
8. Prove full learner+EA irreducibility for the actual coupled transition.
9. Apply the actual full-state self-loop theorem for period 1.
10. Extend CHAD through the entire representation path and close concrete activation-specific Möbius laws.
