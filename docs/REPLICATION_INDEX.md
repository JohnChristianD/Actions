# Replication index

Authoritative mathematical layer: Agda `--safe`.

Current GitHub Actions safe gate: `.github/workflows/agda.yml`.
Current canonical manifest: `.ci/canonical-module.txt`.

## Actual exploration methods

- `Exotic/ERL/Exploration/OpenESDyadic.agda` — scalar `Int8` quotient.
- `Exotic/ERL/Exploration/MR15Reachability.agda` — full two-coordinate softsign-gated representation state.
- `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda` — whole coupled learner/noise state; Noisy Nets is a coupled ablation, not a detached explorer.

Probability laws are parameters to these methods, not separate explorers.

## Retained law frontier

- `Exotic/ERL/Exploration/FlatDyadic.agda` — uniform weight `1` over all `256` Int8 residues.
- `Exotic/ERL/Exploration/DyadicLadder.agda` — exact dyadic-shell law with denominator `32`, zero weight `16`, and unit mass on every signed power-of-two shell through `±128`.
- `Exotic/ERL/Exploration/DyadicLaw.agda` exposes exactly these two retained laws.

The legacy triangular family, geometric-5 candidate, Lazy Walk, and other non-flat/non-dyadic-shell candidates are permanently absent from the selectable theorem surface.

## Endogenous theorem boundary

`Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda` composes a retained law with one actual method only after exact law normalization/unit-support, finite `signReLU8 -> softsign8` forward/pullback composition, conditional Möbius forward closure, the canonical softsign-gated `PeriodOne`, irreducibility, and self-loop are present. `PeriodOne` is derived inside the composed object.

`.ci/discovery/ExplorationTheoremGenerator.hs` enumerates exactly six retained law×method compositions and runs the generated Agda harness under `--safe`.

## Canonical exploration boundary

`Exotic/ERL/FullCoupled/SoftsignGatedRepresentation.agda` is the canonical representation theorem state: `Int8 × Int8` after the signReLU8→softsign8 forward activation boundary.

OpenES is its scalar quotient. MR15 is the full representation-level exploration theorem. Noisy Nets is the coupled-state refinement.

## Strict method theorem ordering

`Exotic/ERL/FullCoupled/TheoremStrengthV3.agda` derives the strict factor-extension chain:

`OpenES < MR15 < NoisyNet`.

MR15 projects to OpenES by forgetting the second representation coordinate. Noisy Nets projects to MR15 through the explicit bridge in `Exotic/ERL/FullCoupled/NoisyNetSoftsignFactor.agda`. The factor relation is transitive in-tree, so the Noisy-Net→OpenES factor is explicitly constructed by composition. Each strict link includes a section/retraction and a proper-fiber separator.

This is a theorem-factor ordering, not an empirical performance ranking.

## Möbius status

`Exotic/efficient_chad/SoftsignGatedComposition.agda` proves finite CHAD composition for the abstract finite `softsign8 ∘ signReLU8` operator boundary. `Exotic/efficient_chad/MobiusInt8Composition.agda` proves finite Möbius-action closure under composition.

`Exotic/efficient_chad/MobiusSoftsignBridge.agda` proves conditional forward Möbius closure for the composed activation from concrete signReLU8 and softsign8 witnesses. The full-coupling record now carries this composition theorem; activation-specific witnesses are still required before an actual activation-specific Möbius certificate can be claimed.

## Noisy-Net representation bridge

`Exotic/ERL/FullCoupled/NoisyNetSoftsignFactor.agda` contains the concrete projection, section/retraction, step projection, and step lifting required for the strict theorem ordering.

The full theorem ledger is maintained in `docs/THEOREM_FIRST_REPLICATION_WIKI.md`.
