# Replication index

Authoritative mathematical layer: Agda `--safe`.

Current GitHub Actions safe gate: `.github/workflows/agda.yml`.
Current canonical manifest: `.ci/canonical-module.txt`.

Current manifest entries:

- `Exotic/ERL/FullCoupled/AllSafeCombined.agda`
- `Exotic/ERL/FullCoupled/AllSafeCombined_test.agda`

The broader v147 closure target is described in `Agda/README.md`; promote it to CI authority only when the exact source path exists in-tree and is wired into the manifest.

The full theorem ledger and replication rules are maintained in `docs/THEOREM_FIRST_REPLICATION_WIKI.md`.

The CI gate enforces a permanent finite theorem-scope exclusion check with `.ci/check-forbidden-theorems.py` before Agda verification. The repository remains finite/dyadic/Int8-oriented; excluded theorem families cannot return through source, documentation, generated candidates, or metadata.

Live actual exploration methods are:

- `Exotic/ERL/Exploration/MR15Reachability.agda`
- `Exotic/ERL/Exploration/OpenESDyadic.agda`
- `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda`

Probability-law modules are separate from exploration methods:

- `Exotic/ERL/Exploration/LazyWalkDyadic.agda`
- `Exotic/ERL/Exploration/DyadicLadder.agda`
- `Exotic/ERL/Exploration/FlatDyadic.agda`
- `Exotic/ERL/Exploration/DyadicLaw.agda`

The reusable graph theorem schema is `Exotic/ERL/Exploration/ExplorationTheoremSchema.agda`.

`Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda` is the theorem boundary. A law and an actual explorer are accepted together; the composed object also records the representation-layer boundary, and `PeriodOne` is derived only from the concrete irreducibility and self-loop proofs.

`.ci/discovery/ExplorationTheoremGenerator.hs` enumerates the three actual explorers against all three checked probability laws and writes exactly nine endogenous theorem objects to `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`. Haskell constructs source and invokes `agda --safe`; it never upgrades a conjecture into a theorem.

The current finite theorem universe is therefore the Cartesian product:

`{MR15, OpenES, NoisyNet} × {LazyWalk, DyadicLadder, FlatDyadic}`.

The standalone pure-DMCP distribution module was removed and is not a live canonical probability layer.

Noisy Nets remains part of the coupled learner theorem surface, not a detached law file. The current coupled module carries the finite gate identity and explicit whole-state irreducibility/self-loop proof terms for its fresh-target abstraction.

The representation theorem boundary is the finite `softsign8 ∘ signReLU8` CHAD composition in `Exotic/efficient_chad/SoftsignGatedComposition.agda`, followed by GateNN and projection in the intended forward path. Concrete activation-specific Möbius laws remain kernel-checked dependencies rather than generated assertions.
