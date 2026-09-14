# Replication index

Authoritative mathematical layer: Agda `--safe`.

Current GitHub Actions safe gate: `.github/workflows/agda.yml`.
Current canonical manifest: `.ci/canonical-module.txt`.

## Actual exploration methods

- `Exotic/ERL/Exploration/OpenESDyadic.agda` — scalar `Int8` quotient.
- `Exotic/ERL/Exploration/MR15Reachability.agda` — representation-level exploration state.
- `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda` — coupled learner/noise ablation.

Probability laws are parameters to exploration, not separate explorers.

## Retained law frontier

- `Exotic/ERL/Exploration/FlatDyadic.agda` — uniform weight `1` over all `256` Int8 residues.
- `Exotic/ERL/Exploration/DyadicLaw.agda` — exposes exactly `flatDyadic`.

All present non-flat probability families are outside the selectable theorem surface.

## Canonical recurrent representation boundary

`Exotic/ERL/FullCoupled/GRUComposition.agda` records the active composition boundary:

`dyadic RoPE (Walsh-Rademacher) -> sparsemax -> frozen Haar -> specialized GRU -> Pi`.

No standalone pointwise activation or MLP is inserted between attention and the GRU. The GRU alone owns the retained nonlinear maps `0.5*(1+softsign)` and `signReLU`.

## GRU recurrent noise

`Exotic/ERL/FullCoupled/GRUNoisyNetState.agda` exposes exactly three perturbable recurrent matrices `U_z,U_r,U_h` plus hidden state. For width `2`, the state has `14` Int8 coordinates and therefore `256^14` possible states before optimizer or auxiliary coordinates are added.

## Möbius and scan theorems

`Exotic/efficient_chad/GRUGatedComposition.agda` contains the finite CHAD composition and pointwise sequential Möbius witness interface inside the GRU gates.

`Exotic/efficient_chad/GRURecurrentMobius.agda` proves associative finite window composition and the exact reassociation law required for parallel scan.

The new recurrence class is algebraically richer than a one-step feed-forward composition because windows compose as a finite action monoid. A strict state-strength relation from the old Noisy-Net carrier to the new GRU carrier remains a separate projection/lift theorem.

## Global optimization and norm boundary

`GRUComposition` retains the global optimizer, global L2, global F4-Int(U), softsign-q-IDBD, Efficient-CHAD, sparsemax/GRU L1-plus-path-one obligations, exact decorrelation, and frozen feature witnesses as one theorem ledger.

## Legacy factor theorem

The prior `OpenES < MR15 < NoisyNet` factor chain remains a valid legacy theorem for the previous finite carriers. It is not silently reused as a GRU strictness proof.
