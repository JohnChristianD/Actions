# Replication index

Authoritative mathematical layer: Agda `--safe`.

Current GitHub Actions safe gate: `.github/workflows/agda.yml`.
Current canonical manifest: `.ci/canonical-module.txt`.

## Actual exploration methods

- `Exotic/ERL/Exploration/OpenESDyadic.agda` — scalar `Int8` quotient.
- `Exotic/ERL/Exploration/MR15Reachability.agda` — two-coordinate softsign-gated representation state.
- `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda` — whole coupled learner state.

## Retained laws

- `Exotic/ERL/Exploration/LazyWalkDyadic.agda`.
- `Exotic/ERL/Exploration/DyadicLadder.agda`.
- `Exotic/ERL/Exploration/DyadicGeometric5.agda`.
- `Exotic/ERL/Exploration/DyadicLaw.agda` exposes exactly these three.

The legacy triangular family and Flat Dyadic are permanently absent from the selectable theorem surface.

## Endogenous theorem boundary

`Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda` composes one law with one actual method only after exact law normalization/unit-support, the finite `signReLU8 -> softsign8` forward/pullback composition, irreducibility, and self-loop are present. `PeriodOne` is derived inside the composed object.

`.ci/discovery/ExplorationTheoremGenerator.hs` enumerates exactly nine law×method compositions and runs the generated Agda harness under `--safe`.

## Strict method theorem ordering

`Exotic/ERL/FullCoupled/TheoremStrengthV3.agda` derives the strict method chain from actual state factors:

`OpenES < MR15 < NoisyNet`.

MR15 projects to OpenES by forgetting a real representation coordinate; NoisyNet projects to MR15 by hiding `sigma3`. Both strict links carry explicit same-projection/distinct-state witnesses.

## Möbius status

`Exotic/efficient_chad/SoftsignGatedComposition.agda` proves finite CHAD composition for the concrete forward pair. `Exotic/efficient_chad/MobiusInt8Composition.agda` proves finite Möbius-action closure under composition.

The concrete activation-specific Möbius witness for `signReLUQ8` and `softsignQ8` remains unpromoted until Agda checks the actual finite witness.

## Noisy-Net representation bridge

`Exotic/ERL/FullCoupled/SoftsignGatedRepresentation.agda` contains the projection, section/retraction, step projection, and step lifting required for the strict theorem ordering.

The full theorem ledger is maintained in `docs/THEOREM_FIRST_REPLICATION_WIKI.md`.
