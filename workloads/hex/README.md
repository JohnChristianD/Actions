# Hex upstream workload reference

Upstream project: https://git.sr.ht/~h3rald/hex
GitHub mirror: https://github.com/h3rald/hex
Requested source: `src/hex.c`
Repository copy: `workloads/hex/src/hex.c`
Inspected upstream reference recorded by the repository: `add4081ef80f5f9b6ff89dcc3d847964a4fe00d6`
Upstream source license: MIT

The requested source is now vendored under `workloads/hex/src/hex.c` with its MIT license retained at `workloads/hex/LICENSE`. The checked source contains no standalone Tcl, Tk, tcl, or tk sites, so there was nothing in `src/hex.c` to rewrite as Mirth.

Mirth now serves as the general-purpose workload adapter. Agda `--safe` remains semantic and proof authority, while Mercury remains graph/discovery infrastructure. The vendored Hex interpreter is workload provenance and implementation material, not a second theorem authority.
