{
  description = "Reproducible discovery tooling for the canonical Agda learner/EA proof surface";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f (import nixpkgs { inherit system; }));
    in {
      formatter = forAllSystems (pkgs: pkgs.nixpkgs-fmt);

      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          packages = [
            pkgs.git
            pkgs.bash
            pkgs.coreutils
            pkgs.gnugrep
            pkgs.gawk
            pkgs.haskellPackages.ghc
            pkgs.haskellPackages.cabal-install
          ];
          shellHook = ''
            export LC_ALL=C
            export LANG=C
          '';
        };
      });

      checks = forAllSystems (pkgs: {
        discovery-toolchain = pkgs.runCommand "discovery-toolchain" { } ''
          ${pkgs.haskellPackages.ghc}/bin/runghc --version > $out
          ${pkgs.haskellPackages.cabal-install}/bin/cabal --version >> $out
          ${pkgs.bash}/bin/bash --version >> $out
        '';
      });
    };
}
