{
  description = "Pinned Nix environment for the Agda kernel, Mercury e-graph, and typed Dhall CI scripting";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/0439f75413ace6c42e4c722cafd4d6e5401de648";
    vehicle = {
      url = "github:vehicle-lang/vehicle/6312434dfc109a800c618c4c6a43089b116b7c42";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, vehicle }:
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

      agdaWithStdlib = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.agdaPackages.agda.withPackages [ pkgs.agdaPackages.standard-library ];

      haskellLiquidGhc = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.haskellPackages.ghcWithPackages (p: [
          p.rio
          p.liquidhaskell
        ]);

      liquidHaskellEnv = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.mkShell {
          packages = [
            (haskellLiquidGhc system)
            pkgs.z3
            pkgs.coreutils
            pkgs.findutils
            pkgs.git
          ];
          shellHook = ''
            export LIQUID_SOLVER=z3
          '';
        };

    in
    {
      vehicleAgdaSource = "${vehicle}/vehicle-agda/src";

      packages = forAllSystems (system:
        let
          pkgs = pkgsFor system;
        in
        {
          agda = agdaWithStdlib system;
          ci = pkgs.haskellPackages.dhall;
          yamlscript = pkgs.yamlscript;
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

          malonzo-extract = let
            script = pkgs.writeShellApplication {
              name = "malonzo-extract";
              runtimeInputs = [
                (agdaWithStdlib system)
                (haskellLiquidGhc system)
                pkgs.coreutils
                pkgs.findutils
              ];
              text = ''
                set -euo pipefail
                out="build/malonzo";
                rm -rf "$out"
                mkdir -p "$out"
                export AGDA_COMMAND="${agdaWithStdlib system}/bin/agda"
                "$AGDA_COMMAND" -l standard-library -i . --compile --no-main --compile-dir="$out" FullCoupled/CanonicalLearnerMonolith.agda
                "$AGDA_COMMAND" -l standard-library -i . --compile --no-main --compile-dir="$out" FullCoupled/TheoremsMonolith.agda
                find "$out/MAlonzo/Code" -type f -name '*.hs' -print | sort
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/malonzo-extract";
          };

          agda-haskell-pipeline = let
            script = pkgs.writeShellApplication {
              name = "agda-haskell-pipeline";
              runtimeInputs = [
                (agdaWithStdlib system)
                (haskellLiquidGhc system)
                pkgs.z3
                pkgs.coreutils
                pkgs.findutils
                pkgs.mirth
                pkgs.stdenv.cc
              ];
              text = ''
                set -euo pipefail
                out="build/agda-haskell"
                rm -rf "$out"
                mkdir -p "$out"
                export AGDA_COMMAND="${agdaWithStdlib system}/bin/agda"
                "$AGDA_COMMAND" -l standard-library -i . --compile --no-main --compile-dir="$out" FullCoupled/CanonicalLearnerMonolith.agda
                "$AGDA_COMMAND" -l standard-library -i . --compile --no-main --compile-dir="$out" FullCoupled/TheoremsMonolith.agda
                generated_learner="$out/MAlonzo/Code/FullCoupled/CanonicalLearnerMonolith.hs"
                generated_theorem="$out/MAlonzo/Code/FullCoupled/TheoremsMonolith.hs"
                liquid_sync_c="$out/liquid-haskell-sync.c"
                liquid_sync="$out/liquid-haskell-sync"
                liquid_target="$out/LiquidGeneratedBridge.hs"
                mirthc .ci/mirth/liquid_haskell_sync.mth -o "$liquid_sync_c"
                cc -std=c99 "$liquid_sync_c" -o "$liquid_sync"
                "$liquid_sync" "$generated_learner" "$generated_theorem" "$liquid_target"
                liquid --smtsolver=z3 -i "$out" "$liquid_target"
                printf '%s\n' \
                  "source=FullCoupled/CanonicalLearnerMonolith.agda generated=MAlonzo/Code/FullCoupled/CanonicalLearnerMonolith.hs target=build/agda-haskell/LiquidGeneratedBridge.hs liquid:z3:pass" \
                  "source=FullCoupled/TheoremsMonolith.agda generated=MAlonzo/Code/FullCoupled/TheoremsMonolith.hs target=build/agda-haskell/LiquidGeneratedBridge.hs liquid:z3:pass" \
                  > "$out/liquid-agda-manifest.tsv"
                cat "$out/liquid-agda-manifest.tsv"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/agda-haskell-pipeline";
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
          liquid-haskell = liquidHaskellEnv system;

          default = pkgs.mkShell {
            packages = [
              pkgs.mercury
              pkgs.haskellPackages.dhall
              (haskellLiquidGhc system)
              pkgs.z3
              pkgs.haskellPackages.dhall-json
              pkgs.mirth
              pkgs.gh
              (agdaWithStdlib system)
              pkgs.stdenv.cc
              pkgs.yamlscript
              pkgs.elmPackages.elm
            ];
            shellHook = ''
              export PATH="${pkgs.mercury}/bin:$PATH"
              export AGDA_COMMAND="${agdaWithStdlib system}/bin/agda"
              export LIQUID_SOLVER=z3
              export VEHICLE_AGDA_SOURCE="${vehicle}/vehicle-agda/src"
            '';
          };
        });
    };
}