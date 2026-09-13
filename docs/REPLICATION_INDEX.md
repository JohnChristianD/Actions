# Replication index

Authoritative mathematical layer: Agda `--safe`.

Current GitHub Actions safe gate: `.github/workflows/agda.yml`.
Current canonical manifest: `.ci/canonical-module.txt`.

Current manifest entries:

- `Exotic/ERL/FullCoupled/AllSafeCombined.agda`
- `Exotic/ERL/FullCoupled/AllSafeCombined_test.agda`

The broader v147 closure target is described in `Agda/README.md`; promote it to CI authority only when the exact source path exists in-tree and is wired into the manifest.

The full theorem ledger, endogenous theorem targets, distribution/mutation ablation classes, iid/expectation boundary, CHAD scope, conjecture-generator design, Cabal/GHC/Nix/Guix facts, and the next replication prompt are maintained in:

`docs/THEOREM_FIRST_REPLICATION_WIKI.md`

Live ERL source surfaces include:

- `Exotic/ERL/Exploration/DMCPDistribution.agda`
- `Exotic/ERL/Exploration/MR15Reachability.agda`
- `Exotic/ERL/Exploration/OpenESDyadic.agda`
- `Exotic/ERL/Stages/Stage02_CHAD.agda`
- `Exotic/ERL/Stages/Stage03_LinearLearner.agda`
- `Exotic/ERL/Stages/Stage05_Representation.agda`
- `Exotic/ERL/Stages/Stage06_CoupledLearner.agda`

`MR15Reachability.agda` currently proves a negative result for the present mutation relation: a population-uniform invariant blocks global reachability, so the current relation is not irreducible. This remains a required repair target rather than an assumption.
