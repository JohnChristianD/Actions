# Replication index

Authoritative mathematical layer: Agda `--safe`.

Current GitHub Actions safe gate: `.github/workflows/agda.yml`.
Current canonical manifest: `.ci/canonical-module.txt`.

## GRU exploration theorem class

`Exotic/ERL/Exploration/GRUPerturbationMethods.agda` is the active finite comparison surface for:

- `GRU-OpenES`
- `GRU-MR15`
- `GRU-NoisyNet`

The three currently share the same finite GRU carrier and fresh-target exploration shell. Therefore they inherit the same exact irreducibility, self-loop, period-one, and aperiodicity witnesses. A strict ranking requires concrete method-specific carriers plus projection/lift/retraction and a proper fiber; no legacy factor ordering is reused.

## Retained law frontier

- `Exotic/ERL/Exploration/FlatDyadic.agda` — uniform weight `1` over all `256` Int8 residues.
- `Exotic/ERL/Exploration/DyadicLaw.agda` — exposes exactly `flatDyadic`.

All present non-flat probability families are outside the selectable theorem surface.

## Canonical recurrent representation boundary

`Exotic/ERL/FullCoupled/GRUComposition.agda` records the active composition boundary:

`dyadic RoPE (Walsh-Rademacher) -> sparsemax -> frozen Haar -> specialized GRU -> Pi`.

No standalone pointwise activation or MLP is inserted between attention and the GRU. The retained nonlinear maps live inside the GRU gates: `0.5*(1+softsign)` and `signReLU`.

## GRU recurrent noise

`Exotic/ERL/FullCoupled/GRUNoisyNetState.agda` exposes exactly three perturbable recurrent matrices `U_z,U_r,U_h` plus hidden state. For width `2`, the persistent state has `14` Int8 coordinates and therefore `256^14` possible states before optimizer or auxiliary coordinates are added.

The module now contains explicit `Irreducible`, `SelfLoop`, `PeriodOne`, and finite `Aperiodic` witnesses for the fresh-target GRU exploration shell.

## Möbius and scan theorems

`Exotic/efficient_chad/GRUGatedComposition.agda` contains the finite CHAD composition and pointwise sequential Möbius witness interface inside the GRU gates.

`Exotic/efficient_chad/GRURecurrentMobius.agda` proves associative finite window composition and the exact reassociation law required for parallel scan.

The recurrence is algebraically richer than a one-step feed-forward composition because windows compose as finite actions. This does not by itself prove a strict state-strength ordering among the three perturbation methods.

## Global optimization, norms, and actor-critic boundary

`GRUComposition` keeps explicit theorem boundaries for the GRU/sparsemax L1-plus-path-one pair, the global L2 regularizer, the global optimizer/F4-Int(U)/softsign-q-IDBD ledger, and an Int8 actor/critic boundary with an explicit DPG-update obligation.

The repository already has an Int8 shared actor/critic construction, but the GRU-specific DPG update theorem is still a separate proof obligation; Int8 typing alone does not establish it.

## Pruned surfaces

The standalone softsign-gated representation, standalone pointwise activation helper, pointwise softsign Möbius bridge, legacy Noisy-Net toy carrier, and old strict-factor theorem modules have been removed from the active tree.
