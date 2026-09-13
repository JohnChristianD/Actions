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

The canonical probability-law surface contains exactly one law:

- `Exotic/ERL/Exploration/FlatDyadic.agda`
- `Exotic/ERL/Exploration/DyadicLaw.agda`

Flat Dyadic gives exact denominator 256 and positive support for every Int8 code. It therefore proves one-step complete code support, strictly stronger than a mere ±1 generator witness.

`Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda` is the theorem boundary. A law and an actual explorer are accepted together; the composed object also records the softsign-gated CHAD boundary, universal law support, concrete irreducibility, self-loop, and derived `PeriodOne`.

`.ci/discovery/ExplorationTheoremGenerator.hs` enumerates the three actual explorers against the one retained law and writes exactly three endogenous theorem objects to `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda`. Haskell constructs source and invokes `agda --safe`; it never upgrades a conjecture into a theorem.

The current theorem universe is:

`{MR15, OpenES, NoisyNet} × {FlatDyadic}`.

The Noisy-Net method now has a concrete projection/lift theorem at `Exotic/ERL/FullCoupled/NoisyNetRepresentationProjection.agda`: the coupled state projects to the pre-softsign Int8 representation, the forward observable is `softsignQ8 (signReLUQ8 x)`, representation steps lift to coupled steps, coupled steps project back, and distinct GateParams can lie in the same representation fiber.

Thus the strict theorem frontier currently established is:

`softsign-gated representation < NoisyNet coupled state`,

with Flat Dyadic the unique maximal retained probability law. The maximal connected theorem corner is `NoisyNet × FlatDyadic`. MR15 and OpenES remain unranked against NoisyNet until their own production-state projection/lift theorems exist and pass `agda --safe`.

The standalone pure-DMCP distribution module was removed and is not a live canonical probability layer.
