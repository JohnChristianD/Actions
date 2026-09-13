{
  description = "Reproducible discovery tooling for the canonical Agda learner/EA proof surface";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f (import nixpkgs { inherit system; }));
    in {
      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          packages = [
            pkgs.git
            pkgs.haskellPackages.ghc
            pkgs.haskellPackages.cabal-install
          ];
        };
      });
    };
}
