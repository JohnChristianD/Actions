# Modular replication layout

The canonical replication path is the staged Agda DAG, not the monolithic CompleteSafe file.

Run Stage01 through Stage08 independently, then run `ModularCanonical.agda` as the modular root. Keep `CompleteSafe_v147.agda` as a compatibility regression target until its legacy scope surface is fully normalized.

The companion CSV layout is `docs/MODULAR_REPLICATION_LAYOUT.csv`; measured task returns are stored directly and independently from proof/oracle status.
