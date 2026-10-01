{
  description = "Pinned Nix environment for the Agda kernel, Mercury e-graph, and typed Dhall CI scripting";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/cac0437206a9c9aefa161dae30cee71170d60088";
    vehicle = {
      url = "github:vehicle-lang/vehicle/6312434dfc109a800c618c4c6a43089b116b7c42";
      flake = false;
    };
    schmitty = {
      url = "github:wenkokke/schmitty/9a85ee0ecec1f477cc803b8af66567bd36487a2b";
      flake = false;
    };
    agdarsec = {
      url = "github:gallais/agdarsec/03b8c4ec57b8bc9517b5bc2fca8a540e1ec858f0";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, vehicle, schmitty, agdarsec }:
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
      vehicleAgdaSource = "${vehicle}/vehicle-agda/src";
      schmittyAgdaSource = "${schmitty}/src";
      agdarsecAgdaSource = "${agdarsec}/src";

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
          mirth-fast-dirty-source = let
            script = pkgs.writeShellApplication {
              name = "mirth-fast-dirty-source";
              runtimeInputs = [ pkgs.coreutils ];
              text = ''
                set -euo pipefail
                cat .ci/mirth/agda_to_elm.mth
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-fast-dirty-source";
          };
          mirth-c99-sync = let
            script = pkgs.writeShellApplication {
              name = "mirth-c99-sync";
              runtimeInputs = [ pkgs.mirth pkgs.stdenv.cc pkgs.coreutils ];
              text = ''
                set -euo pipefail
                test "$#" = 1
                output="$1"
                tmp=$(mktemp -d)
                trap 'rm -rf "$tmp"' EXIT
                mirthc .ci/mirth/agda_to_elm.mth -o "$tmp/agda-to-elm.c"
                cc -std=c99 "$tmp/agda-to-elm.c" -o "$output"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-c99-sync";
          };
          mirth-agda-import-sync = let
            script = pkgs.writeShellApplication {
              name = "mirth-agda-import-sync";
              runtimeInputs = [
                pkgs.mirth
                pkgs.stdenv.cc
                pkgs.coreutils
                pkgs.git
              ];
              text = ''
                set -euo pipefail
                tmp=$(mktemp -d)
                trap 'rm -rf "$tmp"' EXIT
                mirthc .ci/mirth/agda_import_sync.mth -o "$tmp/agda-import-sync.c"
                cc -std=c99 "$tmp/agda-import-sync.c" -o "$tmp/agda-import-sync"
                "$tmp/agda-import-sync" | bash -s -- "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-agda-import-sync";
          };

          mirth-ascii-sync = let
            script = pkgs.writeShellApplication {
              name = "mirth-ascii-sync";
              runtimeInputs = [
                pkgs.mirth
                pkgs.stdenv.cc
                pkgs.coreutils
                pkgs.git
              ];
              text = ''
                set -euo pipefail
                tmp=$(mktemp -d)
                trap 'rm -rf "$tmp"' EXIT
                mirthc .ci/mirth/ascii_surface.mth -o "$tmp/ascii-surface.c"
                cc -std=c99 "$tmp/ascii-surface.c" -o "$tmp/ascii-surface"
                "$tmp/ascii-surface" | bash
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-ascii-sync";
          };

          mirth-agda-graph = let
            script = pkgs.writeShellApplication {
              name = "mirth-agda-graph";
              runtimeInputs = [
                pkgs.mirth
                pkgs.stdenv.cc
                pkgs.coreutils
              ];
              text = ''
                set -euo pipefail
                tmp=$(mktemp -d)
                trap 'rm -rf "$tmp"' EXIT
                mirthc .ci/mirth/agda_graph.mth -o "$tmp/agda-graph.c"
                cc -std=c99 "$tmp/agda-graph.c" -o "$tmp/agda-graph"
                "$tmp/agda-graph" "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-agda-graph";
          };

          readme-doc-sync = let
            script = pkgs.writeShellApplication {
              name = "readme-doc-sync";
              runtimeInputs = [
                pkgs.coreutils
                pkgs.git
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
              pkgs.mirth
              pkgs.gh
              pkgs.stdenv.cc
              pkgs.z3
              pkgs.elmPackages.elm
            ];
            shellHook = ''
              export PATH="\${pkgs.mercury}/bin:$PATH"
              export VEHICLE_AGDA_SOURCE="\${vehicle}/vehicle-agda/src"
              export SCHMITTY_AGDA_SOURCE="\${schmitty}/src"
              export AGDARSEC_AGDA_SOURCE="\${agdarsec}/src"
            '';
          };
        });
    };
}