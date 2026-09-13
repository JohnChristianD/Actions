# Replication index

Authoritative mathematical layer: Agda `--safe`.

Current GitHub Actions safe gate: `.github/workflows/agda.yml`.
Current canonical manifest: `.ci/canonical-module.txt`.

Current manifest entries:

- `Exotic/ERL/FullCoupled/AllSafeCombined.agda`
- `Exotic/ERL/FullCoupled/AllSafeCombined_test.agda`

The broader v147 closure target is promoted only when the exact source path exists in-tree and is wired into the manifest.

## Actual exploration methods

- `Exotic/ERL/Exploration/OpenESDyadic.agda` — scalar Int8 quotient.
- `Exotic/ERL/Exploration/MR15Reachability.agda` — canonical two-coordinate softsign-gated representation state.
- `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda` — whole coupled learner state with mutable GateParams.

## Retained probability laws

- `Exotic/ERL/Exploration/LazyWalkDyadic.agda`.
- `Exotic/ERL/Exploration/DyadicLadder.agda`.
- `Exotic/ERL/Exploration/DyadicGeometric5.agda`.
- `Exotic/ERL/Exploration/DyadicLaw.agda` exposes exactly those three laws.

The former triangular family and Flat Dyadic are permanently absent from the selectable law surface. The geometric law is the retained contiguous symmetric scale-geometric candidate; Ladder remains a multiscale shell ablation.

## Endogenous theorem boundary

`Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda` composes one law with one actual method only after exact law normalization/unit-support, the finite `signReLU8 -> softsign8` forward/pullback composition, irreducibility, and self-loop are present. `PeriodOne` is then derived inside the composed object.

`.ci/discovery/ExplorationTheoremGenerator.hs` enumerates exactly nine law×method compositions and runs the generated Agda harness under `--safe`.

## Strict method theorem ordering

`Exotic/ERL/FullCoupled/TheoremStrengthV3.agda` derives the method ordering from actual state factors:

`OpenES < MR15 < NoisyNet`.

The MR15-to-OpenES projection forgets one genuine representation coordinate. The NoisyNet-to-MR15 projection forgets hidden `sigma3`. Each strict link has an explicit same-projection/distinct-state witness.

Therefore the strict maximum on the method axis is Noisy Nets, independent of statistical comparison.

## Möbius status

`Exotic/efficient_chad/SoftsignGatedComposition.agda` proves finite CHAD composition for the concrete forward pair. `Exotic/efficient_chad/MobiusInt8Composition.agda` proves finite Möbius-action closure under composition.

The activation-specific implication from the concrete quantized `signReLUQ8` and `softsignQ8` definitions to a Möbius witness is not promoted until its actual finite witness is checked by Agda. Generic composition closure is not treated as that witness.

## Noisy-Net representation bridge

`Exotic/ERL/FullCoupled/SoftsignGatedRepresentation.agda` is the canonical factor bridge from the full coupled learner to the representation exploration layer. It contains the projection, section/retraction, step projection, and step lifting the strict method ordering requires.

The full theorem ledger is maintained in `docs/THEOREM_FIRST_REPLICATION_WIKI.md`.
