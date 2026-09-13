# Replication index

Authoritative mathematical layer: Agda `--safe`.

Current GitHub Actions safe gate: `.github/workflows/agda.yml`.
Current canonical manifest: `.ci/canonical-module.txt`.

Current manifest entries:

- `Exotic/ERL/FullCoupled/AllSafeCombined.agda`
- `Exotic/ERL/FullCoupled/AllSafeCombined_test.agda`

The broader v147 closure target is described in `Agda/README.md`; promote it to CI authority only when the exact source path exists in-tree and is wired into the manifest.

The full theorem ledger and replication rules are maintained in `docs/THEOREM_FIRST_REPLICATION_WIKI.md`.

Live theorem surfaces now center on three exploration mechanisms:

- `Exotic/ERL/Exploration/MR15Reachability.agda`
- `Exotic/ERL/Exploration/OpenESDyadic.agda`
- `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda`

The reusable graph theorem schema is `Exotic/ERL/Exploration/ExplorationTheoremSchema.agda`.

`.ci/discovery/ExplorationTheoremGenerator.hs` automatically checks each method for concrete irreducibility/self-loop proof symbols and runs `agda --safe` when those proofs exist. The generated report is `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`.

The status distinction is deliberate: `Proven` requires a concrete proof surface plus successful `agda --safe`; `MissingProof` means the theorem obligation is not yet closed; `AgdaFailure` means the claimed proof surface does not typecheck safely.

The standalone pure-DMCP distribution module was removed. DMCP is not a live canonical exploration module.

`MR15Reachability.agda` must not be read as proof that the repaired independent-tick MR15 is irreducible. The current repository tree still requires the actual repaired MR15 implementation and its concrete reachability proof before canonical promotion.

Noisy Nets is part of the coupled learner theorem surface, not a detached distribution file. `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda` carries the finite gate identity and explicit irreducibility/self-loop theorem types; concrete proof terms remain required before those properties are marked proven.
