{
  description = "Pinned Nix environment for the Agda kernel, Mercury e-graph, and typed Dhall CI scripting";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/0439f75413ace6c42e4c722cafd4d6e5401de648";
    agda-prelude = {
      url = "github:UlfNorell/agda-prelude/4230566d3ae229b6a00258587651ac7bfd38d088";
      flake = false;
    };
    typetopology = {
      url = "github:martinescardo/TypeTopology/8761920fdaec20c9dada7ff1d6628c09491245c5";
      flake = false;
    };
    agda2hs = {
      url = "github:agda/agda2hs/4e6de7ec2109b3bed6a820728b57d31ad7ffd698";
    };
  };

  outputs = { self, nixpkgs, agda-prelude, typetopology, agda2hs }:
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
          libraryName = "agda-prelude";
          libraryFile = "agda-prelude.agda-lib";
          dontBuild = true;
          installPhase = ''
            mkdir -p "$out/src"
            cp -R src/. "$out/src/"
            cp agda-prelude.agda-lib "$out/agda-prelude.agda-lib"
          '';
          meta = {
            description = "Minimal Agda programming prelude";
            homepage = "https://github.com/UlfNorell/agda-prelude";
            license = pkgs.lib.licenses.mit;
          };
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
          meta = {
            description = "Logical manifestations of topological concepts via univalent mathematics";
            homepage = "https://github.com/martinescardo/TypeTopology";
            license = pkgs.lib.licenses.gpl3Only;
          };
        };

      agda2hsBaseLib = system:
        agda2hs.packages.${system}.base-lib;

      agdaWithTheoremGraphLibraries = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.writeShellApplication {
          name = "agda-with-theorem-graph";
          runtimeInputs = [ pkgs.agdaPackages.agda pkgs.coreutils ];
          text = ''
            set -euo pipefail
            tmp=$(mktemp -d)
            trap 'rm -rf "$tmp"' EXIT
            mkdir -p "$tmp/agda-prelude" "$tmp/TypeTopology" "$tmp/agda2hs-base"
            cp -R "${agdaPreludeLib system}/src/." "$tmp/agda-prelude/"
            cp -R "${typeTopologyLib system}/source/." "$tmp/TypeTopology/"
            cp -R "${agda2hsBaseLib system}/." "$tmp/agda2hs-base/"
            exec ${pkgs.agdaPackages.agda}/bin/agda \
              -i "$tmp/agda-prelude" \
              -i "$tmp/TypeTopology" \
              -i "$tmp/agda2hs-base" \
              "$@"
          '';
        };

      agdaWithPrelude = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.writeShellApplication {
          name = "agda-with-prelude";
          runtimeInputs = [ pkgs.agdaPackages.agda pkgs.coreutils ];
          text = ''
            set -euo pipefail
            tmp=$(mktemp -d)
            trap 'rm -rf "$tmp"' EXIT
            mkdir -p "$tmp/agda-prelude" "$tmp/TypeTopology" "$tmp/agda2hs-base"
            cp -R "${agdaPreludeLib system}/src/." "$tmp/agda-prelude/"
            cp -R "${typeTopologyLib system}/source/." "$tmp/TypeTopology/"
            cp -R "${agda2hsBaseLib system}/." "$tmp/agda2hs-base/"
            exec ${pkgs.agdaPackages.agda}/bin/agda \
              -i "$tmp/agda-prelude" \
              -i "$tmp/TypeTopology" \
              -i "$tmp/agda2hs-base" \
              "$@"
          '';
        };
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
      packages = forAllSystems (system:
        let
          pkgs = pkgsFor system;
        in
        {
          agda = agdaWithPrelude system;
          agda2hs = agda2hsWithHaskell system;
          agda-prelude = agdaPreludeLib system;
          typetopology = typeTopologyLib system;
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
              runtimeInputs = [ pkgs.coreutils pkgs.git ];
              text = ''
                set -euo pipefail
                bash .ci/mirth/agda_import_sync.sh "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-agda-import-sync";
          };

          mirth-agda-command-sync = let
            script = pkgs.writeShellApplication {
              name = "mirth-agda-command-sync";
              runtimeInputs = [ pkgs.coreutils pkgs.git ];
              text = ''
                set -euo pipefail
                bash .ci/mirth/agda_command_sync.sh "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-agda-command-sync";
          };

          mirth-agda-sync = let
            script = pkgs.writeShellApplication {
              name = "mirth-agda-sync";
              runtimeInputs = [ pkgs.coreutils pkgs.git ];
              text = ''
                set -euo pipefail
                bash .ci/mirth/agda_import_sync.sh "$@"
                bash .ci/mirth/agda_command_sync.sh "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-agda-sync";
          };

          mirth-ascii-sync = let
            script = pkgs.writeShellApplication {
              name = "mirth-ascii-sync";
              runtimeInputs = [ pkgs.coreutils pkgs.git ];
              text = ''
                set -euo pipefail
                bash .ci/mirth/ascii_surface.sh
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-ascii-sync";
          };

          mirth-agda-graph = let
            script = pkgs.writeShellApplication {
              name = "mirth-agda-graph";
              runtimeInputs = [ pkgs.coreutils pkgs.git ];
              text = ''
                set -euo pipefail
                bash .ci/mirth/agda_graph.sh "$@"
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
                "${agda2hsWithHaskell system}/bin/agda2hs" -i . FullCoupled/Agda2HsSurface.agda -o "$out"
                test -s "$out/FullCoupled/Agda2HsSurface.hs"
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
                pkgs.git
                pkgs.mirth
                pkgs.stdenv.cc
              ];
              text = ''
                set -euo pipefail
                out="build/agda-haskell"
                rm -rf "$out"
                mkdir -p "$out"
                "${agda2hsWithHaskell system}/bin/agda2hs" -i . FullCoupled/Agda2HsSurface.agda -o "$out"
                test -s "$out/FullCoupled/Agda2HsSurface.hs"
                mkdir -p "$out/ghc"
                "${haskellLiquidGhc system}/bin/ghc" -package rio -fplugin=LiquidHaskell -i "$out" -odir "$out/ghc" -hidir "$out/ghc" -c "$out/FullCoupled/Agda2HsSurface.hs"
                liquid --smtsolver=z3 -i "$out" "$out/FullCoupled/Agda2HsSurface.hs"
                printf '%s\n' \
                  "source=FullCoupled/Agda2HsSurface.agda generated=build/agda-haskell/FullCoupled/Agda2HsSurface.hs ghc:pass liquid:z3:pass" \
                  > "$out/agda2hs-liquid-manifest.tsv"
                cat "$out/agda2hs-liquid-manifest.tsv"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/agda-haskell-pipeline";
          };

          mercury-theorem-e2e = let
            script = pkgs.writeShellApplication {
              name = "mercury-theorem-e2e";
              runtimeInputs = [
                (agdaWithTheoremGraphLibraries system)
                (agda2hsWithHaskell system)
                pkgs.mercury
                pkgs.haskellPackages.dhall
                pkgs.coreutils
                pkgs.git
              ];
              text = ''
                set -euo pipefail
                test -f FullCoupled/TheoremsMonolith.agda
                agda="${agdaWithTheoremGraphLibraries system}/bin/agda-with-theorem-graph"
                agda2hs="${agda2hsWithHaskell system}/bin/agda2hs"
                semantic_manifest="$PWD/.ci/discovery/.semantic-source-files"
                interpolation_manifest="$PWD/.ci/discovery/.interpolation-imports"
                agda2hs_out=$(mktemp -d)
                dependency_graph="$agda2hs_out/theorem-imports.dot"
                trap 'rm -rf "$agda2hs_out" "$semantic_manifest" "$interpolation_manifest"' EXIT
                printf '%s\n' \
                  "agda-prelude=${agdaPreludeLib system}" \
                  "TypeTopology=${typeTopologyLib system}" \
                  "agda2hs-base=${agda2hsBaseLib system}" \
                  > "$interpolation_manifest"
                "$agda" --dependency-graph="$dependency_graph" -i . FullCoupled/TheoremsMonolith.agda
                bash .ci/discovery/agda_semantic_source_closure.sh \
                  "$dependency_graph" \
                  "$semantic_manifest" \
                  "$PWD" \
                  "${agdaPreludeLib system}/src" \
                  "${typeTopologyLib system}/source" \
                  "${agda2hsBaseLib system}"
                test -s "$semantic_manifest"
                "$agda2hs" -i . FullCoupled/Agda2HsSurface.agda -o "$agda2hs_out"
                test -s "$agda2hs_out/FullCoupled/Agda2HsSurface.hs"
                cd .ci
                mmc --make check_forbidden_theorems
                ./check_forbidden_theorems
                cd discovery
                mmc --make theorem_registry_reconcile
                ./theorem_registry_reconcile --check
                mmc --make theorem_monolith_egraph_sync
                ./theorem_monolith_egraph_sync
                mmc --make novel_theorem_interpolator
                ./novel_theorem_interpolator
                test -s novel-theorem-interpolation.dhall
                dhall text --file novel-theorem-interpolation.dhall >/dev/null
                report=theorem-monolith-egraph-sync.dhall
                test -s "$report"
                dhall text --file "$report" >/dev/null
                test -s novel-theorem-interpolation.dhall
                dhall text --file novel-theorem-interpolation.dhall >/dev/null
                echo "mercury-theorem-e2e=pass"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mercury-theorem-e2e";
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
              export AGDA_COMMAND="${agdaWithPrelude system}/bin/agda-with-prelude"
              export LIQUID_SOLVER=z3
            '';
          };
        });
    };
}