{
  description = "Pinned Nix environment for the Agda kernel, Mercury e-graph, and typed Dhall CI scripting";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/29c6bca3b9a3ee1263483043c0e50321eb4ec7ae";
  };

  outputs = { self, nixpkgs }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      forAllSystems = nixpkgs.lib.genAttrs systems;

      pkgsFor = system:
        import nixpkgs { inherit system; };
    in
    {
      packages = forAllSystems (system:
        let
          pkgs = pkgsFor system;
        in
        {
          ci = pkgs.haskellPackages.dhall;
          default = pkgs.haskellPackages.dhall;
        });

      apps = forAllSystems (system:
        let
          pkgs = pkgsFor system;
        in
        {
          ci = {
            type = "app";
            program = "${pkgs.haskellPackages.dhall}/bin/dhall";
          };
          elm-graph-build = let
            script = pkgs.writeShellApplication {
              name = "elm-graph-build";
              runtimeInputs = [
                pkgs.coreutils
                pkgs.elmPackages.elm
                pkgs.haskellPackages.dhall
              ];
              text = ''
                set -euo pipefail
                repo_root=$(pwd)
                tmp=$(mktemp -d)
                trap 'rm -rf "$tmp"' EXIT
                mkdir -p "$tmp/src" "$repo_root/workloads/elm-graph/dist"
                cp workloads/elm-graph/src/*.elm "$tmp/src/"
                dhall text --file workloads/elm-graph/elm-project.dhall > "$tmp/elm.json"
                dhall text --file workloads/elm-graph/graph.dhall > "$tmp/src/GeneratedGraph.elm"
                (cd "$tmp" && elm make src/Main.elm                   --optimize                   --output "$repo_root/workloads/elm-graph/dist/elm.js")
                test -s workloads/elm-graph/dist/elm.js
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/elm-graph-build";
          };
          mirth-workload-check = let
            script = pkgs.writeShellApplication {
              name = "mirth-workload-check";
              runtimeInputs = [
                pkgs.mirth
                pkgs.stdenv.cc
              ];
              text = ''
                set -euo pipefail
                tmp=$(mktemp -d)
                trap 'rm -rf "$tmp"' EXIT

                mirthc workloads/mirth/graph_adapter.mth -o "$tmp/graph_adapter.c"
                cc "$tmp/graph_adapter.c" -o "$tmp/graph_adapter"

                actual=$("$tmp/graph_adapter")
                expected=$(cat <<'EOF'
Actions Mirth workload adapter
Semantic authority: Agda --safe
Dependency graph: Mercury
Dhall contract: typed evidence
Nix environment: reproducible composition
Elm graph bundle: workloads/elm-graph/dist/elm.js
EOF
)
                test "$actual" = "$expected"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-workload-check";
          };
          readme-doc-sync = let
            script = pkgs.writeShellApplication {
              name = "readme-doc-sync";
              runtimeInputs = [
                pkgs.coreutils
                pkgs.git
                pkgs.python3
                pkgs.haskellPackages.dhall
              ];
              text = ''
                set -euo pipefail
                generated=$(mktemp)
                trap 'rm -f "$generated"' EXIT
                dhall text --file .ci/readme-doc-sync.dhall > "$generated"
                bash "$generated" "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/readme-doc-sync";
          };
          slow-readme-update = let
            script = pkgs.writeShellApplication {
              name = "slow-readme-update";
              runtimeInputs = [
                pkgs.coreutils
                pkgs.gawk
                pkgs.gnused
                pkgs.git
                pkgs.python3
                pkgs.haskellPackages.dhall
              ];
              text = ''
                generated=$(mktemp)
                trap 'rm -f "$generated"' EXIT
                dhall text --file .ci/slow-readme-update.dhall > "$generated"
                bash "$generated"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/slow-readme-update";
          };
          prune-theorem-registries = let
            script = pkgs.writeShellApplication {
              name = "prune-theorem-registries";
              runtimeInputs = [
                pkgs.mercury
              ];
              text = ''
                set -euo pipefail
                cd .ci/discovery
                mmc --make theorem_registry_reconcile
                ./theorem_registry_reconcile --prune
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/prune-theorem-registries";
          };
          default = {
            type = "app";
            program = "${pkgs.haskellPackages.dhall}/bin/dhall";
          };
        });

      devShells = forAllSystems (system:
        let
          pkgs = pkgsFor system;
        in
        {
          default = pkgs.mkShell {
            packages = [
              pkgs.mercury
              pkgs.haskellPackages.dhall
              pkgs.haskellPackages.dhall-json
              pkgs.gh
              pkgs.python3
              pkgs.mirth
              pkgs.elmPackages.elm
            ];
            shellHook = ''
              export PATH="\${pkgs.mercury}/bin:$PATH"
            '';
          };
        });
    };
}