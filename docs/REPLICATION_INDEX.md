# Replication index

Authoritative mathematical layer: Agda `--safe`.

Current GitHub Actions safe gate: `.github/workflows/agda.yml`.
Current canonical manifest: `.ci/canonical-module.txt`.

## Actual exploration methods

- `Exotic/ERL/Exploration/OpenESDyadic.agda` — scalar `Int8` quotient.
- `Exotic/ERL/Exploration/MR15Reachability.agda` — two-coordinate softsign-gated representation state.
- `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda` — whole coupled learner state.

Probability laws are parameters to these methods, not separate explorers.

## Retained laws

- `Exotic/ERL/Exploration/LazyWalkDyadic.agda`.
- `Exotic/ERL/Exploration/DyadicLadder.agda`.
- `Exotic/ERL/Exploration/FlatDyadic.agda`.
- `Exotic/ERL/Exploration/DyadicLaw.agda` exposes exactly these three.

The legacy triangular family and the scale-misaligned `DyadicGeometric5` candidate are permanently absent from the selectable theorem surface.

## Endogenous theorem boundary

`Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda` composes one retained law with one actual method only after exact law normalization/unit-support, finite `signReLU8 -> softsign8` forward/pullback composition, irreducibility, and self-loop are present. `PeriodOne` is derived inside the composed object.

`.ci/discovery/ExplorationTheoremGenerator.hs` enumerates exactly nine retained law×method compositions and runs the generated Agda harness under `--safe`.

## Strict method theorem ordering

`Exotic/ERL/FullCoupled/TheoremStrengthV3.agda` derives the strict factor-extension chain:

`OpenES < MR15 < NoisyNet`.

MR15 projects to OpenES by forgetting the second representation coordinate. Noisy Nets projects to MR15 through the explicit bridge in `Exotic/ERL/FullCoupled/NoisyNetSoftsignFactor.agda`, which hides the coupled `sigma3` coordinate. Both strict links carry same-projection/distinct-state witnesses.

This is a theorem-factor ordering, not an empirical performance ranking.

## Möbius status

`Exotic/efficient_chad/SoftsignGatedComposition.agda` proves finite CHAD composition for the abstract finite `softsign8 ∘ signReLU8` operator boundary. `Exotic/efficient_chad/MobiusInt8Composition.agda` proves finite Möbius-action closure under composition.

The concrete activation-specific Möbius witness for the repository's signReLU8/softsign8 implementation remains a separate Agda obligation and is not fabricated by the generic composition law.

## Noisy-Net representation bridge

`Exotic/ERL/FullCoupled/SoftsignGatedRepresentation.agda` defines the canonical representation state and step relation.

`Exotic/ERL/FullCoupled/NoisyNetSoftsignFactor.agda` contains the concrete projection, section/retraction, step projection, and step lifting required for the strict theorem ordering.

The full theorem ledger is maintained in `docs/THEOREM_FIRST_REPLICATION_WIKI.md`.
