# Change record — 2026-09-29

Scope: isolated Min / Gforth / gbForth / Factor / Pony lab under one top-level folder.

Request: add Pony through Nixpkgs and provide runnable example code using the existing isolated language lab pattern.

Before:
- `forth-lab/` contained Min, Gforth, gbForth, and Factor examples.
- No Pony compiler or Pony example existed.

Now:
- `forth-lab/flake.nix` adds `pkgs.ponyc` from the pinned Nixpkgs 26.05 input.
- `forth-lab/examples/ponyc/hello/main.pony` is a runnable Pony program with `actor Main` and a `create` constructor that prints through `Env.out`.
- `forth-lab/verify.sh` compiles the Pony package in an isolated temporary directory and runs the resulting `hello` binary.
- `forth-lab/README.md` documents Pony setup and execution.
- Existing root flake, Agda proof sources, theorem monoliths, and existing CI remain untouched.

Why:
Keep language experiments isolated while proving each sample has a real compiler entry point and runtime path.

When not to use:
Do not promote Pony into the root Nix environment unless the repository explicitly adopts Pony as a repository dependency.

Technical reasoning:
- Nixpkgs 26.05 provides `ponyc` version 0.64.0 and supports the four systems already declared by this lab: `x86_64-linux`, `x86_64-darwin`, `aarch64-linux`, and `aarch64-darwin`.
- Pony documentation defines the `Main` actor constructor as the executable entry point and shows `ponyc` compiling a package directory into an executable with the package directory name.
- Verification copies the example package into a temporary directory before compiling, so generated compiler artifacts never alter tracked source.

Operational consequence:
Entering `forth-lab` still bootstraps Min once through Nimble. Pony is Nix-managed through the same pinned `nixpkgs` input as the other maintained tools.

Verification evidence:
`bash verify.sh` is the focused lab gate. It executes Min, Gforth, and Factor where supported, compiles gbForth to a non-empty ROM, and compiles/runs the Pony example.

Future implications:
_Unknown - ask the owner and record the answer._

Stale when:
Update this record if Nixpkgs changes Pony package availability/platforms, the Pony example entry point changes, or `forth-lab` becomes a repository-wide dependency.

Upstream references:
- Pony hello world: https://tutorial.ponylang.io/getting-started/hello-world.html
- Pony runtime/compiler: https://www.ponylang.io/
- Nixpkgs Pony package: https://github.com/NixOS/nixpkgs/tree/nixos-26.05/pkgs/by-name/po/ponyc
