# Change record — 2026-09-29

Scope: isolated Min / Gforth / gbForth lab under one new top-level folder.

Request: add a separate Nix flake, examples, and keep all existing learner/proof files untouched.

Before:
- No dedicated Min/Forth/gbForth playground existed.
- Existing root Nix and Agda surfaces were unrelated to this request.

Now:
- `forth-lab/flake.nix` provides an isolated development shell.
- Gforth and gbForth come from the flake's pinned Nixpkgs input.
- Min is installed into local ignored bootstrap state through Nimble on first shell entry.
- Three example sources live only under `forth-lab/examples/`.
- No existing source, root flake, theorem monolith, CI lane, or learner file is modified.

Why:
Keep experimental language tooling outside the canonical learner and proof system.

When not to use:
Do not copy this flake into the root Nix environment. Keep language experiments isolated unless they become an explicit repository dependency.

Operational consequence:
Entering `forth-lab` requires network access once to bootstrap Min through Nimble. Gforth and gbForth remain Nix-managed.

Stale when:
Update this record if the folder becomes a repository-wide dependency or Min gets a maintained Nixpkgs package.
