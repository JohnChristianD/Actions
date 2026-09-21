# Typed CI orchestration

The canonical CI control plane is implemented in `.ci/actions_ci.ml`, built and packaged by `.ci/ci.nix` through the pinned nixpkgs OCaml package set.

Nix remains the declarative build/environment layer. OCaml owns process orchestration and repository-surface checks. Mercury owns theorem semantic extraction, A*-ordered dependency discovery, e-graph saturation, analysis, and cost-guided extraction. Agda `--safe` remains proof authority.

The workflow enters the Nix devshell and executes `actions-ci`; the devshell supplies Mercury and the compiled OCaml executable. This removes the previous hand-maintained shell control program without introducing another runtime scripting dependency.

The graph contract remains source-derived:

`TheoremsMonolith.agda`
→ semantic law extraction
→ A* cost-guided dependency paths
→ e-graph insertion/saturation
→ extraction
→ JSON sync report

The current CI surface explicitly allows the canonical OCaml orchestrator and continues rejecting the previously retired scripting/source languages.
