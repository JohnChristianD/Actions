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

Lazy Walk and Dyadic Ladder are probability-law modules, not additional exploration methods.

`Exotic/ERL/Exploration/LazyWalkDyadic.agda` defines a finite common-denominator-4 law with exact stay/forward/backward masses and proves normalization plus positive zero/unit support.

`Exotic/ERL/Exploration/DyadicLadder.agda` defines a finite common-denominator-32 law with a stay mass and signed power-of-two outcomes and proves normalization plus positive unit support.

`Exotic/ERL/Exploration/DyadicLaw.agda` is the law interface. It exposes only the two accepted finite laws to the composition generator.

## Endogenous law × method theorem class

The theorem frontier is the Cartesian product

`{MR15, OpenES, NoisyNet} × {LazyWalk, DyadicLadder}`.

A law is not promoted to a theorem on its own. The theorem object exists only at the full algebraic coupling boundary:

`law + actual explorer + irreducibility + self-loop -> PeriodOne`.

`Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda` carries the exact law-normalization proof together with the actual explorer irreducibility/self-loop proofs and derives `PeriodOne` through `periodOne-from-components`.

The Haskell discovery generator enumerates all six permutations and writes them into `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`. Haskell constructs source only; Agda `--safe` decides acceptance.

The six generated theorem objects are:

- `MR15LazyWalkEndogenous`
- `MR15DyadicLadderEndogenous`
- `OpenESLazyWalkEndogenous`
- `OpenESDyadicLadderEndogenous`
- `NoisyNetLazyWalkEndogenous`
- `NoisyNetDyadicLadderEndogenous`

No standalone law `PeriodOne` theorem is generated.

## Full-state theorem discipline

For a transition relation `_—→_`:

`Irreducible = ∀ s t → Reach _—→_ s t`.

`SelfLoop = ∀ s → s —→ s`.

The reusable sufficient package is `Irreducible × SelfLoop -> PeriodOne`.

This is deliberately a full-state statement. Exploration-only reachability does not substitute for learner+EA reachability. The current MR15 and OpenES modules remain explicit finite kernel abstractions until their production mutation/selection transitions are connected. Noisy Nets is already represented on the coupled learner state.

## Mutation and finite probability

For an additive coordinate over `Z_256`, the generator target is `gcd(256,S) = 1` for the effective positive-probability increment support `S`.

A one-step self-loop requires effective support containing `0` with positive mass.

Fresh finite noise per tick is the theorem-friendly mutation model because it preserves explicit support witnesses and finite product constructions.

## CHAD and activation composition

CHAD proves the correctness of a differential/VJP interface for a defined computation. Normalization, support, irreducibility, communicating classes, and period remain separate finite-state theorems.

The repository has an exact `CHADOperator` composition theorem in `Exotic/efficient_chad/Int8.agda`. It can compose future concrete finite operators in the intended order:

`signReLU8 -> softsign8 -> GateNN -> Pi`.

Concrete activation-specific VJP or Möbius results still require the corresponding in-tree definitions; the generic composition theorem does not invent missing operator semantics.

## External Efficient-CHAD boundary

CI audits Tom Smeding's upstream source in a clean `.ci/external/efficient-chad-agda` checkout and probes the existing proof under the installed Agda toolchain. No new package or project-local Agda library is added by this audit. The upstream file and its own checked-in dependencies remain outside the repository theorem authority.

## Gating-layer counterfactual

`GatingLayerCounterfactual.agda` proves that gate reachability can lift through an explicit full-state lift, while gate-only exploration is insufficient for global full-state irreducibility when a distinct non-gating factor is preserved. Therefore whole-state communication must be proved on the actual coupled transition.

## Fitness theorem

The finite VEB-RL-style `-TD` fitness surface uses exact dyadic histogram masses, exact normalization, ordinal/rank ordering, and exact sorting whenever rank consistency is part of the theorem.

## Replication order

1. Keep pure DMCP artifacts deleted.
2. Enforce the permanent finite/dyadic theorem-scope exclusions.
3. Keep Lazy Walk and Dyadic Ladder as exact probability-law modules only.
4. Keep MR15, OpenES, and Noisy Nets as the actual explorer set.
5. Generate every law × method permutation through the full algebraic coupling boundary.
6. Require concrete Agda `--safe` proof terms for every generated theorem object.
7. Connect each finite kernel to its production transition semantics before upgrading theorem status.
8. Prove full learner+EA irreducibility for the actual coupled transition.
9. Apply the actual full-state self-loop theorem for period 1.
10. Extend CHAD through the entire representation path.
