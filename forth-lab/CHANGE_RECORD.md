# Change record — 2026-09-29

Scope: isolated Min / Gforth / gbForth / Factor lab under one top-level folder.

Request: add Factor to the existing isolated language lab and verify examples are runnable rather than merely present.

Before:
- `forth-lab/` contained Min, Gforth, and gbForth examples.
- The gbForth example defined an empty `main`; it produced a valid ROM but intentionally did nothing.
- No Factor runtime or Factor example existed.

Now:
- `forth-lab/flake.nix` adds Nixpkgs `factorPackages.factor-minimal` on `x86_64-linux`.
- `forth-lab/examples/factor/hello.factor` is a runnable Factor script that prints a greeting.
- `forth-lab/examples/min/squares.min` remains a runnable Min program.
- `forth-lab/examples/gforth/hello.fs` remains a runnable Gforth program.
- `forth-lab/examples/gbforth/hello.fs` now initializes the Game Boy text terminal and renders `Hello World!` from `main`.
- `forth-lab/verify.sh` executes Min, Gforth, and Factor when supported and compiles gbForth, requiring a non-empty ROM.
- No root flake, Agda source, theorem monolith, or existing CI lane is modified.

Why:
Keep language experiments isolated while making each example traceable to a real executable entry path.

When not to use:
Do not move these runtimes into the root Nix environment unless the repository explicitly adopts one of them as a dependency.

Technical reasoning:
- Factor uses Nixpkgs' maintained Factor packaging instead of a second bootstrap path.
- Nixpkgs currently exposes the Factor runtime through `factorPackages` and its Factor derivation targets `x86_64-linux`; the flake therefore conditionally installs Factor only on that host.
- gbForth's official hello-world guide shows `main` calling `install-font`, `init-term`, and `.`" Hello World"` to produce visible ROM behavior.

Operational consequence:
Entering `forth-lab` still bootstraps Min once through Nimble. Factor is available on `x86_64-linux`; other declared flake systems retain the existing Min/Gforth/gbForth shell without a non-buildable Factor package.

Verification evidence:
`bash verify.sh` is the focused local gate for this folder. It checks process output for Min, Gforth, and Factor and checks that gbForth emits a non-empty ROM.

Future implications:
_Unknown - ask the owner and record the answer._

Stale when:
Update this record if the folder becomes a repository-wide dependency, Factor gains supported Nixpkgs builds on additional systems, or example entry points change.

Upstream references:
- Factor: https://www.factorcode.org/
- Factor command-line scripts: https://docs.factorcode.org/content/article-command-line.html
- gbForth hello world: https://gbforth.org/hello-world.html
- Min: https://min-lang.org/
