# Modular CI rules

The staged proof DAG is the preferred reproducibility interface.

The standalone modular gate checks Stage01 through Stage08 and `ModularCanonical.agda`. The monolithic CompleteSafe check remains a regression check while its legacy scope/notation is being normalized.

External oracle jobs are optional diagnostics. They do not gate theorem validity unless a workflow explicitly defines them as evidence-only checks.

All source repair is deterministic Python 3 running on the GitHub Ubuntu runner before Agda. The repair layer is never imported into the Agda semantics.
