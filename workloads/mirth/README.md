# Mirth workload adapter

This directory replaces the former Tcl/Tk workload surface with Mirth.

The adapter is deliberately presentation-neutral: it validates that a general-purpose workload can sit downstream from the same Agda and Mercury semantic boundary without adding a second theorem model. It reports the generated Elm graph bundle rather than making a GUI toolkit part of the semantic contract.

Mirth is compiled with `mirthc -c` in CI. The semantic core remains Agda `--safe`; Mercury remains declaration and graph infrastructure.

Upstream Mirth: https://git.sr.ht/~typeswitch/mirth
