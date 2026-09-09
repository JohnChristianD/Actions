# Modular replication layout

The canonical replication path is the staged Agda DAG, not the monolithic CompleteSafe file.

Run Stage01 through Stage08 independently, then run `ModularCanonical.agda` as the modular root. Keep `CompleteSafe_v147.agda` as a compatibility regression target until its legacy scope surface is fully normalized.

The companion CSV layout is `docs/MODULAR_REPLICATION_LAYOUT.csv`; measured task returns are stored directly and independently from proof/oracle status.

The full wiki-ready replication contract is `docs/CORSANE_2022_MODULAR_REPLICATION_PROMPT.md`. It records the current finite algebra boundary, L1/L2 LayerNorm treatment, Efficient-CHAD status, Gallici theorem extraction, theorem/conjecture split, missing replication items, and the next dependency-ordered closure steps.

The repository's security-oriented workflow checks are an orthogonal engineering layer. They do not replace the Agda kernel gate or exact-rational oracle gate.