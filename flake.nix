{
  description = "Pinned Nix environment for the Agda kernel and Mercury e-graph lanes";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/29c6bca3b9a3ee1263483043c0e50321eb4ec7ae";


    agda-stdlib = {
      url = "github:agda/agda-stdlib/v2.4";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, agda-stdlib }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      forAllSystems = nixpkgs.lib.genAttrs systems;

      mkPkgs = system:
        import nixpkgs { inherit system; };
    in
    {
      devShells = forAllSystems (system:
        let
          pkgs = mkPkgs system;

          agda = pkgs.agdaPackages.agda;
        in
        {
          default = pkgs.mkShell {
            packages = [
              agda
              pkgs.mercury
              pkgs.gnumake
              pkgs.git
            ];

            shellHook = ''
              export AGDA_STDLIB="${agda-stdlib}/src"
              printf 'agda=%s\n' "$(agda --version | head -n 1)"
              printf 'mercury=%s\n' "$(mmc --version | head -n 1)"
            '';
          };
        });
    };
}
