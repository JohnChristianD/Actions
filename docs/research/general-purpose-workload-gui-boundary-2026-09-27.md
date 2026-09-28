# General-purpose workload and semantic boundary — 2026-09-28

## Decision

The repository keeps one semantic authority and makes workload implementation language-agnostic.

1. Agda `--safe` owns canonical definitions, typed obligations, and proofs.
2. Mercury owns declaration extraction, dependency discovery, and graph processing.
3. Dhall owns typed verification/evidence contracts.
4. Nix owns reproducible environment composition.
5. Workloads are replaceable implementations consuming explicit contracts.

The workload language is therefore orthogonal to theorem authority. A workload may be C, Haskell, Mirth, Lua, Factor, or another general-purpose language without changing the proof architecture, provided it does not introduce a second canonical semantic model.

## Current workload

The current prompt-scoped adapter is Mirth at `workloads/mirth/graph-adapter.mth`. It is intentionally presentation-neutral. It reports the generated Elm graph artifact and makes no GUI toolkit part of the semantic interface.

Mirth is a practical fit for this boundary because its current compiler is a strongly typed concatenative language compiler and nixpkgs packages it as `mirthc`. The workload adapter remains replaceable; Agda and Mercury do not depend on Mirth syntax.

## E-graph and A* seam

The proof strategy remains:

```
Agda --safe theorem declarations
          |
          v
Mercury declaration extraction
          |
          v
A* / e-graph dependency search
          |
          v
candidate path / equivalence certificate
          |
          v
Agda proof term or explicit witness boundary
```

Graph reachability is not itself proof. Promotion requires a proposition in the Agda theorem surface and acceptance by safe Agda. This lets the same semantic core feed xmonad-, dwm-, st-, or other workload adapters without duplicating theorem definitions.

## Hex provenance

The requested H3RALD `hex` source is now vendored at `workloads/hex/src/hex.c`, with its MIT license retained. The checked source is a small concatenative C implementation with 32-bit hexadecimal integers, strings, quotations, global symbols, a REPL, and native symbols.

The source has no standalone Tcl/Tk sites, so there was no Tcl/Tk code inside `src/hex.c` to translate. Vendoring it preserves provenance and workload material; it does not create a second semantic authority.

## Orthogonality requirement

The language-independent rule is narrower than "every implementation is interchangeable in every operational detail."

An implementation language must:
- consume an explicit workload contract;
- avoid becoming a second definition of canonical learner semantics;
- remain outside the Agda proof source unless an explicit proof/refinement interface is added;
- remain independently packageable on target systems.

A runtime dependency is justified by a concrete workload. It is not justified merely by candidate-language enumeration.

The old Tcl/Tk adapter was therefore a concrete workload choice, not an architectural requirement. Replacing it with Mirth changes the workload implementation and CI checks, not the Agda/Mercury semantic roles.

## Platform boundary

microOS/Aeon, NixOS, VanillaOS, Guix, and similar Linux systems do not alter this semantic rule. Desktop integration is an adapter concern. A future xmonad/dwm/st/lambdock workload can select its native host language while the theorem/e-graph core remains unchanged.

## Evidence

- Agda `--safe` disables features that can introduce inconsistency, including postulates, incomplete proofs, non-strictly-positive datatypes, disabled termination checks, and universe inconsistencies. citeturn540323search7
- Mercury documents itself as a general-purpose declarative language with strong types, modes, determinism, modules, higher-order programming, and a formal declarative semantics. citeturn540323search3turn540323search6turn540323search9
- Mirth's current compiler repository describes Mirth as a strongly typed concatenative language; its nixpkgs package exposes `mirthc`. citeturn690307search1turn690307search0

## Provenance

The latest Actions commit before this workload migration only refreshed README commit-totality metadata. The semantic workload boundary comes from the preceding Hex/Mirth provenance commits. This migration makes that boundary executable: Mirth is a real package/runtime dependency, Tcl/Tk are removed from the current workload surface, and Hex source is vendored for provenance.
