{
  description = "Pinned Nix environment for the Agda kernel, typed semantic search, and Dhall CI scripting";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/0439f75413ace6c42e4c722cafd4d6e5401de648";
    nixpkgs-ghc924.url = "github:NixOS/nixpkgs/a62e6edd6d5e1fa0329b8653c801147986f8d446";
    typetopology = {
      url = "github:martinescardo/TypeTopology/8761920fdaec20c9dada7ff1d6628c09491245c5";
      flake = false;
    };
    agda2hs = {
      url = "github:agda/agda2hs/4e6de7ec2109b3bed6a820728b57d31ad7ffd698";
    };
  };

  outputs = {
    self,
    nixpkgs,
    nixpkgs-ghc924,
    typetopology,
    agda2hs
  }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      forAllSystems = nixpkgs.lib.genAttrs systems;

      pkgsFor = system:
        import nixpkgs {
          inherit system;
          config.allowBroken = true;
        };

      canonicalHaskellPackages = system:
        let
          pkgs = import nixpkgs-ghc924 {
            inherit system;
            config.allowBroken = true;
          };
        in
        pkgs.haskell.packages.ghc924.extend (final: prev: {
          tree-monad =
            pkgs.haskell.lib.overrideCabal
              (final.callHackage "tree-monad" "0.3.2" {})
              (_: {
                postPatch = ''
                  substituteInPlace tree-monad.cabal \
                    --replace-fail '<4.16.3' '<4.17'
                '';
              });
          parallel-tree-search =
            pkgs.haskell.lib.overrideCabal
              (final.callHackage "parallel-tree-search" "0.4.2" {})
              (_: {
                postPatch = ''
                  substituteInPlace parallel-tree-search.cabal \
                    --replace-warn '< 4.15' '< 4.17' \
                    --replace-warn '< 4.16' '< 4.17'
                '';
              });
          smtlib-backends-process =
            pkgs.haskell.lib.overrideCabal prev.smtlib-backends-process (drv: {
              testSystemDepends = (drv.testSystemDepends or [ ]) ++ [ pkgs.z3 ];
            });
        });

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

      agdaEmacs = system:
        let
          pkgs = pkgsFor system;
        in
        (pkgs.emacsPackagesFor pkgs.emacs).emacsWithPackages (epkgs: [
          epkgs.agda2-mode
        ]);

      agdaForShell = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.writeShellApplication {
          name = "agda";
          runtimeInputs = [ (agdaWithLibraries system) ];
          text = ''
            set -euo pipefail
            exec agda-with-libraries "$@"
          '';
        };


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
            mkdir -p "$tmp/TypeTopology" "$tmp/agda2hs-base"
            cp -R "${typeTopologyLib system}/source/." "$tmp/TypeTopology/"
            cp -R "${agda2hsBaseLib system}/." "$tmp/agda2hs-base/"
            chmod -R u+rwX "$tmp/TypeTopology" "$tmp/agda2hs-base"
            exec ${pkgs.agdaPackages.agda}/bin/agda \
              -i "$tmp/TypeTopology" \
              -i "$tmp/agda2hs-base" \
              "$@"
          '';
        };

      agdaWithLibraries = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.writeShellApplication {
          name = "agda-with-libraries";
          runtimeInputs = [ pkgs.agdaPackages.agda pkgs.coreutils ];
          text = ''
            set -euo pipefail
            tmp=$(mktemp -d)
            trap 'rm -rf "$tmp"' EXIT
            mkdir -p "$tmp/TypeTopology" "$tmp/agda2hs-base"
            cp -R "${typeTopologyLib system}/source/." "$tmp/TypeTopology/"
            cp -R "${agda2hsBaseLib system}/." "$tmp/agda2hs-base/"
            chmod -R u+rwX "$tmp/TypeTopology" "$tmp/agda2hs-base"
            exec ${pkgs.agdaPackages.agda}/bin/agda \
              -i "$tmp/TypeTopology" \
              -i "$tmp/agda2hs-base" \
              "$@"
          '';
        };
      ghcLanguageFlags = [
        "-XNoMonomorphismRestriction"
        "-XLocalMonoBinds"
      ];

      ghcGlobalFlags =
        ghcLanguageFlags;

      ghcGlobalFlagsText =
        builtins.concatStringsSep " " ghcGlobalFlags;

      canonicalGhc = system:
        let
          hp = canonicalHaskellPackages system;
        in
        hp.ghcWithPackages (p: [
          p.rio
        ]);

      agda2hsWithHaskell = system:
        let
          ghc = canonicalGhc system;
        in
        agda2hs.packages.${system}.agda2hs.withPackages {
          pkgs = [
            agda2hs.packages.${system}.base-lib
          ];
          inherit ghc;
        };



    in
    {
      packages = forAllSystems (system:
        let
          pkgs = pkgsFor system;
        in
        {
          agda = agdaWithLibraries system;
          agda2hs = agda2hsWithHaskell system;
          typetopology = typeTopologyLib system;
          ci = (canonicalHaskellPackages system).dhall;
          yamlscript = pkgs.yamlscript;
          default = (canonicalHaskellPackages system).dhall;
        });

      apps = forAllSystems (system:
        let
          pkgs = pkgsFor system;
        in
        {
          ci = {
            type = "app";
            program = "${(canonicalHaskellPackages system).dhall}/bin/dhall";
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
          agda2hs-semantic-search = let
            script = pkgs.writeShellApplication {
              name = "agda2hs-semantic-search";
              runtimeInputs = [
                (agdaWithLibraries system)
                (agda2hsWithHaskell system)
                (canonicalGhc system)
                  pkgs.z3
                pkgs.coreutils
                pkgs.git
              ];
              text = ''
                set -euo pipefail
                out="build/agda2hs-semantic-search"
                rm -rf "$out"
                mkdir -p "$out"
                bash .ci/mirth/agda_command_sync.sh --check
                "${agdaWithLibraries system}/bin/agda-with-libraries" --dependency-graph="$out/theorems-monolith.dot" -i . FullCoupled/TheoremsMonolith.agda
                test -s "$out/theorems-monolith.dot"
                bash .ci/discovery/agda_semantic_source_closure.sh \
                  "$out/theorems-monolith.dot" \
                  "$out/.semantic-source-files" \
                  "$PWD/FullCoupled/TheoremsMonolith.agda" \
                  "${typeTopologyLib system}/source" \
                  "${agda2hsBaseLib system}"
                test -s "$out/.semantic-source-files"
                "${agdaWithLibraries system}/bin/agda-with-libraries" -i . FullCoupled/Agda2HsSemanticExtractor.agda
                "${agdaWithLibraries system}/bin/agda-with-libraries" -i . FullCoupled/Agda2HsSemanticSearch.agda
                "${agdaWithLibraries system}/bin/agda-with-libraries" -i . FullCoupled/Agda2HsTheoremGraphEGraph.agda
                "${agda2hsWithHaskell system}/bin/agda2hs" -i . FullCoupled/Agda2HsSemanticExtractor.agda -o "$out"
                "${agda2hsWithHaskell system}/bin/agda2hs" -i . FullCoupled/Agda2HsSemanticSearch.agda -o "$out"
                "${agda2hsWithHaskell system}/bin/agda2hs" -i . FullCoupled/Agda2HsTheoremGraphEGraph.agda -o "$out"
                test -s "$out/FullCoupled/Agda2HsSemanticExtractor.hs"
                test -s "$out/FullCoupled/Agda2HsSemanticSearch.hs"
                test -s "$out/FullCoupled/Agda2HsTheoremGraphEGraph.hs"
                grep -Fq "symbolicEGraphRegression" FullCoupled/Agda2HsTheoremGraphEGraph.agda
                grep -Fq "eGraphAssociativityRegression" FullCoupled/Agda2HsTheoremGraphEGraph.agda
                grep -Fq "requiredTheoremNames" FullCoupled/Agda2HsSemanticSearch.agda
                grep -Fq "requiredPlanComplete" FullCoupled/Agda2HsSemanticSearch.agda
                grep -Fq "inverse-correct" FullCoupled/TheoremsMonolith.agda
                grep -Fq "inverse-csearchable" FullCoupled/TheoremsMonolith.agda
                grep -Fq "inverse-preserves-csearchability" FullCoupled/TheoremsMonolith.agda
                grep -Fq "SearchableEquivalence" FullCoupled/TheoremsMonolith.agda
                ghc \
                  ${builtins.concatStringsSep " " ghcLanguageFlags} \
                  -O0 \
                  -dcore-lint \
                  -i "$out" \
                  -odir "$out/ghc" \
                  -hidir "$out/ghc" \
                  -main-is FullCoupled.Agda2HsSemanticSearch.main \
                  -o "$out/agda2hs-semantic-search" \
                  "$out/FullCoupled/Agda2HsSemanticSearch.hs"
                "$out/agda2hs-semantic-search" > "$out/report.txt"
                grep -Fq "True" "$out/report.txt"
                grep -E '^theorem-graph-edges=[1-9][0-9]* autonomous-a-star-chains=[1-9][0-9]*$' "$out/report.txt"
                grep -E '^agda2hs autonomous theorem-graph A\\*: [1-9][0-9]* dependency chains$' "$out/report.txt"
                grep -Fq "autonomous-regression=True" "$out/report.txt"
                grep -E "^semantic-laws=[1-9][0-9]* nonreflexive=[1-9][0-9]* composite=[1-9][0-9]*$" "$out/report.txt"
                grep -E "^required-plan-count=[1-9][0-9]* required-plan-total=[1-9][0-9]* required-plan-regression=True$" "$out/report.txt"
                grep -Fq "egraph-regression=True egraph-associativity-regression=True" "$out/report.txt"
                printf '%s\n' \
                  "compiler=canonicalHaskellPackages.ghc-9.2.4" \
                  "plugins=none" \
                  "proofKernel=Agda" \
                  "searchKernel=Agda2Hs" \
                  "semanticCompletenessCheck=pass" \
                  "nontrivialCheck=pass" \
                  > "$out/agda2hs-semantic-search-manifest.tsv"
                cat "$out/agda2hs-semantic-search-manifest.tsv"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/agda2hs-semantic-search";
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
                (agdaWithLibraries system)
                (agda2hsWithHaskell system)
                (canonicalGhc system)
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
                "${canonicalGhc system}/bin/ghc" ${ghcGlobalFlagsText} -O0 -dcore-lint -package rio -i "$out" -odir "$out/ghc" -hidir "$out/ghc" -c "$out/FullCoupled/Agda2HsSurface.hs"
                printf '%s\n' \
                  "source=FullCoupled/Agda2HsSurface.agda generated=build/agda-haskell/FullCoupled/Agda2HsSurface.hs ghc:pass" \
                  > "$out/agda2hs-manifest.tsv"
                cat "$out/agda2hs-manifest.tsv"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/agda-haskell-pipeline";
          };

          default = {
            type = "app";
            program = "${(canonicalHaskellPackages system).dhall}/bin/dhall";
          };
        });

      devShells = forAllSystems (system:
        let
          pkgs = pkgsFor system;
        in
        {
          presentation = pkgs.mkShell {
            packages = [
              pkgs.mirth
              pkgs.stdenv.cc
              pkgs.coreutils
              pkgs.findutils
              pkgs.gawk
              pkgs.git
              pkgs.gnugrep
              pkgs.gnused
              pkgs.elmPackages.elm
              pkgs.dhall
              pkgs.dhall-json
            ];
          };

          simple-haskell = pkgs.mkShell {
            packages = [
              (canonicalGhc system)
              pkgs.z3
            ];
            shellHook = ''
              export LIQUID_SOLVER=z3
            '';
          };

          ci = pkgs.mkShell {
            packages = [
              (canonicalHaskellPackages system).dhall
              (agdaWithLibraries system)
              pkgs.coreutils
              pkgs.findutils
              pkgs.git
              pkgs.gh
              pkgs.gnugrep
              pkgs.gnused
            ];
            shellHook = ''
              export AGDA_COMMAND="${agdaWithLibraries system}/bin/agda-with-libraries"
            '';
          };

          ci-versions = pkgs.mkShell {
            packages = [
              (canonicalGhc system)
              (canonicalHaskellPackages system).dhall
              pkgs.z3
              pkgs.mirth
              pkgs.gh
              (agdaWithLibraries system)
              (agdaEmacs system)
            ];
            shellHook = ''
              export AGDA_COMMAND="${agdaWithLibraries system}/bin/agda-with-libraries"
              export LIQUID_SOLVER=z3
            '';
          };

          default = pkgs.mkShell {
            packages = [
              (canonicalHaskellPackages system).dhall
              (canonicalGhc system)
              (canonicalHaskellPackages system).cabal-install
              pkgs.z3
              (canonicalHaskellPackages system).dhall-json
              pkgs.mirth
              pkgs.gh
              (agdaWithLibraries system)
              (agdaForShell system)
              (agdaEmacs system)
              pkgs.stdenv.cc
              pkgs.yamlscript
              pkgs.elmPackages.elm
            ];
            shellHook = ''
              export AGDA_COMMAND="${agdaWithLibraries system}/bin/agda-with-libraries"
              export LIQUID_SOLVER=z3
            '';
          };
        });
    };
}