# Replication index

Authoritative mathematical layer: Agda `--safe`.

Current GitHub Actions safe gate: `.github/workflows/agda.yml`.
Current canonical manifest: `.ci/canonical-module.txt`.

Current manifest entries:

- `Exotic/ERL/FullCoupled/AllSafeCombined.agda`
- `Exotic/ERL/FullCoupled/AllSafeCombined_test.agda`

The broader v147 closure target is described in `Agda/README.md`; promote it to CI authority only when the exact source path exists in-tree and is wired into the manifest.

The full theorem ledger and replication rules are maintained in `docs/THEOREM_FIRST_REPLICATION_WIKI.md`.

The CI gate now enforces a permanent theorem-scope exclusion check with `.ci/check-forbidden-theorems.py` before Agda verification. The repository is strictly finite/dyadic/Int8-oriented; excluded external theorem families cannot return through source, documentation, generated candidates, or metadata.

Live theorem surfaces center on three exploration mechanisms:

- `Exotic/ERL/Exploration/MR15Reachability.agda`
- `Exotic/ERL/Exploration/OpenESDyadic.agda`
- `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda`

The reusable graph theorem schema is `Exotic/ERL/Exploration/ExplorationTheoremSchema.agda`.

`.ci/discovery/ExplorationTheoremGenerator.hs` automatically checks each method for concrete irreducibility/self-loop proof symbols and runs `agda --safe` when those proofs exist. The generated report is `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`.

For theorem breadth, Noisy Nets is the strongest whole-composition candidate because its theorem surface can span finite noise algebra, GateNN identities, coupled-state reachability, full learner+EA reachability, exact VJP/CHAD, and the full-state period theorem. MR15 is the strongest specialized outer-exploration target because its repaired form naturally exposes support/gcd, fresh-tape factorization, self-loop, population reachability, selection compatibility, and coupled-lift obligations. OpenES remains a narrower functional ablation surface.

This ranking is theorem-surface breadth only. It does not assert empirical superiority and does not mark any theorem proven before a concrete Agda `--safe` proof exists.

The status distinction remains deliberate: `Proven` requires a concrete proof surface plus successful `agda --safe`; `MissingProof` means the theorem obligation is not yet closed; `AgdaFailure` means the claimed proof surface does not typecheck safely.

The standalone pure-DMCP distribution module was removed. It is not a live canonical exploration module.

Noisy Nets is part of the coupled learner theorem surface, not a detached distribution file. `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda` carries the finite gate identity and explicit irreducibility/self-loop theorem types; concrete proof terms remain required before those properties are marked proven.
