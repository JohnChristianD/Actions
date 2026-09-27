# General-purpose workload and GUI boundary — 2026-09-27

## Decision

The repository keeps one semantic authority and makes workload implementation language-neutral.

The authoritative layers are:

1. **Agda `--safe`** — canonical definitions, typed obligations, and proofs.
2. **Mercury** — declaration extraction, dependency discovery, and graph processing.
3. **Dhall** — typed verification/evidence contract.
4. **Nix** — reproducible environment and composition.
5. **Workloads** — replaceable implementations that consume explicit contracts.

A workload implementation may use Go, Nim, Lua, Tcl/Tk, Chibi Scheme, Roc, Swift, or another language when the workload has a demonstrated need. Adding such a language does not authorize a second semantic model. The canonical learner meaning remains in the Agda surface.

The CI surface consequently checks the semantic boundary directly: exactly two tracked Agda sources remain the proof surface, while implementation-language suffixes are not treated as semantic violations.

## GUI boundary

Tk should remain an adapter, not the semantic or systems core.

For Linux desktop targets such as microOS/Aeon, NixOS, VanillaOS, and similar systems, a native Tk adapter is a valid optional GUI implementation. It avoids making a browser runtime part of the desktop contract.

A WebAssembly GUI is useful as a separate browser target when browser delivery is a real product requirement. It should expose the same workload contract through a browser host rather than redefining the desktop GUI contract.

The key distinction is:

```
Agda semantic contract
        |
        +--> native workload --> native GUI adapter (optional Tk)
        |
        +--> WASM workload   --> browser GUI adapter (optional)
```

Do not make “Tk in WebAssembly” the canonical GUI. The direct Tk project remains the desktop toolkit; browser-oriented Tk-compatible work such as wTk implements a Tcl-compatible/widget layer through browser technologies instead of becoming a universal Tk backend. A direct Tk/WASM build would therefore be a platform-porting project, not merely a packaging toggle.

## Non-requirements

- Guix is not required.
- Mermaid is not required.
- No GUI toolkit becomes semantic authority.
- No implementation language may duplicate the Agda semantic model.
- No browser dependency is required for native Linux workloads.

## Evidence

- Tk source distribution: https://github.com/tcltk/tk
- Emscripten WebAssembly build documentation: https://emscripten.org/docs/compiling/WebAssembly.html
- wTk browser toolkit: https://core.tcl-lang.org/wtk/home
- Tcl/Tk developer site: https://web.tcl-lang.org/

## Provenance

Before: CI rejected several implementation-language suffixes, including Lua, Nim, and Roc, even though the intended architecture was becoming language-agnostic.

Change: remove language bans from the CI surface, retain exact two-file Agda authority, document the workload boundary, and define native Tk plus optional browser/WASM as separate presentation adapters.

Now: semantic authority remains singular while future general-purpose workloads can choose their implementation language without changing the proof architecture.

Alternatives considered:
- Make Tk/WASM the only GUI: rejected because it makes browser hosting a requirement for Linux desktop delivery and confuses a presentation adapter with the system contract.
- Add every candidate language as a mandatory dependency: rejected because that recreates toolchain duplication without a demonstrated workload need.
