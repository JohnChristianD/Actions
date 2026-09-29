# Mirth workload adapter

This directory replaces the former Tcl/Tk workload surface with Mirth.

The adapter is deliberately presentation-neutral: it validates that a general-purpose workload can sit downstream from the same Agda and Mercury semantic boundary without adding a second theorem model. It reports the generated Elm graph bundle rather than making a GUI toolkit part of the semantic contract.

CI uses the pinned Nix Mirth package to compile `graph_adapter.mth` to C, compile the generated C, execute the workload, and assert its output. The semantic core remains Agda `--safe`; Mercury remains declaration and graph infrastructure.

Upstream Mirth: https://git.sr.ht/~typeswitch/mirth
