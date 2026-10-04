{
  description = "Pinned Nix environment for the Agda kernel, Mercury e-graph, and typed Dhall CI scripting";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/0439f75413ace6c42e4c722cafd4d6e5401de648";
    vehicle = {
      url = "github:vehicle-lang/vehicle/6312434dfc109a800c618c4c6a43089b116b7c42";
      flake = false;
    };
    agda-prelude = {
      url = "github:UlfNorell/agda-prelude/4230566d3ae229b6a00258587651ac7bfd38d088";
      flake = false;
    };
    typetopology = {
      url = "github:martinescardo/TypeTopology/8761920fdaec20c9dada7ff1d6628c09491245c5";
      flake = false;
    };
    extensiontypes-agda = {
      url = "github:nicolaikraus/extensiontypes-agda/0444e27c878842eb7bbabbaaf3c104934a199c3f";
      flake = false;
    };
    two-level-tt = {
      url = "github:ElifUskuplu/2LTT-Agda/b0640910fae9263fe9031636923460dc124920f3";
      flake = false;
    };
    agda2hs = {
      url = "github:agda/agda2hs/4e6de7ec2109b3bed6a820728b57d31ad7ffd698";
    };
  };

  outputs = { self, nixpkgs, vehicle, agda-prelude, typetopology, extensiontypes-agda, two-level-tt, agda2hs }:
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

      agdaPreludeLib = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.agdaPackages.mkDerivation {
          pname = "agda-prelude";
          version = "0-unstable-2026-10-05";
          src = agda-prelude;
          dontBuild = true;
          installPhase = ''
            mkdir -p "$out/src"
            cp -R src/. "$out/src/"
            cp agda-prelude.agda-lib "$out/agda-prelude.agda-lib"
          '';
        };

      typeTopologyLib = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.agdaPackages.mkDerivation {
          pname = "TypeTopology";
          version = "0-unstable-2026-10-05";
          libraryName = "TypeTopology";
          libraryFile = "typetopology.agda-lib";
          src = typetopology;
          dontBuild = true;
          installPhase = ''
            mkdir -p "$out/source"
            cp -R source/. "$out/source/"
            cp typetopology.agda-lib "$out/typetopology.agda-lib"
          '';
        };

      twoLevelTtLib = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.agdaPackages.mkDerivation {
          pname = "two-level-tt";
          version = "0-unstable-2025-08-06";
          libraryName = "two-level-tt";
          libraryFile = "two-level-tt.agda-lib";
          src = two-level-tt;
        };

      extensionPreludeLib = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.agdaPackages.mkDerivation {
          pname = "extension-types";
          version = "0-unstable-2026-07-27";
          libraryName = "extension-types";
          libraryFile = "extension-types.agda-lib";
          src = extensiontypes-agda;
          buildInputs = [ twoLevelTtLib system ];
        };

      agdaWithPrelude = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.agdaPackages.agda.withPackages [
          (agdaPreludeLib system)
          (typeTopologyLib system)
          (extensionPreludeLib system)
        ];

      haskellLiquidGhc = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.haskellPackages.ghcWithPackages (p: [
          p.rio
          p.liquidhaskell
        ]);

      agda2hsWithHaskell = system:
        let
          ghc = haskellLiquidGhc system;
        in
        agda2hs.packages.${system}.agda2hs.withPackages {
          pkgs = [
            agda2hs.packages.${system}.base-lib
          ];
          inherit ghc;
        };

      liquidHaskellEnv = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.mkShell {
          packages = [
            (haskellLiquidGhc system)
            pkgs.haskellPackages.liquidhaskell
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
          agda = agdaWithPrelude system;
          agda2hs = agda2hsWithHaskell system;
          agda-prelude = agdaPreludeLib system;
          typetopology = typeTopologyLib system;
          extension-prelude = extensionPreludeLib system;
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

          agda2hs-extract = let
            script = pkgs.writeShellApplication {
              name = "agda2hs-extract";
              runtimeInputs = [
                (agda2hsWithHaskell system)
                pkgs.coreutils
              ];
              text = ''
                set -euo pipefail
                out="build/agda2hs"
                rm -rf "$out"
                mkdir -p "$out"
                "${agda2hsWithHaskell system}/bin/agda2hs" -i . FullCoupled/Agda2HsSurface.agda -o "$out/Agda2HsSurface.hs"
                test -s "$out/Agda2HsSurface.hs"
                echo "agda2hs-extract=pass"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/agda2hs-extract";
          };

          agda-haskell-pipeline = let
            script = pkgs.writeShellApplication {
              name = "agda-haskell-pipeline";
              runtimeInputs = [
                (agdaWithPrelude system)
                (agda2hsWithHaskell system)
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
                "${agda2hsWithHaskell system}/bin/agda2hs" -i . FullCoupled/Agda2HsSurface.agda -o "$out/Agda2HsSurface.hs"
                test -s "$out/Agda2HsSurface.hs"
                mkdir -p "$out/ghc"
                "${haskellLiquidGhc system}/bin/ghc" -package rio -fplugin=LiquidHaskell -i "$out" -odir "$out/ghc" -hidir "$out/ghc" -c "$out/Agda2HsSurface.hs"
                liquid --smtsolver=z3 -i "$out" "$out/Agda2HsSurface.hs"
                printf '%s\n' \
                  "source=FullCoupled/Agda2HsSurface.agda generated=build/agda-haskell/Agda2HsSurface.hs ghc:pass liquid:z3:pass" \
                  > "$out/agda2hs-liquid-manifest.tsv"
                cat "$out/agda2hs-liquid-manifest.tsv"
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

          simple-haskell = pkgs.mkShell {
            packages = [
              (haskellLiquidGhc system)
              pkgs.z3
              pkgs.haskellPackages.rio
            ];
            shellHook = ''
              export LIQUID_SOLVER=z3
            '';
          };

          default = pkgs.mkShell {
            packages = [
              pkgs.mercury
              pkgs.haskellPackages.dhall
              (haskellLiquidGhc system)
              pkgs.haskellPackages.liquidhaskell
              pkgs.haskellPackages.cabal-install
              pkgs.z3
              pkgs.haskellPackages.dhall-json
              pkgs.mirth
              pkgs.gh
              (agdaWithPrelude system)
              pkgs.stdenv.cc
              pkgs.yamlscript
              pkgs.elmPackages.elm
            ];
            shellHook = ''
              export PATH="${pkgs.mercury}/bin:$PATH"
              export AGDA_COMMAND="${agdaWithPrelude system}/bin/agda"
              export LIQUID_SOLVER=z3
              export VEHICLE_AGDA_SOURCE="${vehicle}/vehicle-agda/src"
            '';
          };
        });
    };
}