{
  description = "Pinned Nix environment for the Agda kernel and Mercury e-graph lanes";

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

      mkPkgs = system:
        import nixpkgs { inherit system; };

      ciProgram = system:
        let
          pkgs = mkPkgs system;
        in
        pkgs.callPackage ./.ci/ci.nix {};

    in
    {
      packages = forAllSystems (system: {
        ci = ciProgram system;
        default = ciProgram system;
      });

      apps = forAllSystems (system: {
        ci = {
          type = "app";
          program = "${ciProgram system}/bin/actions-ci";
        };
        default = {
          type = "app";
          program = "${ciProgram system}/bin/actions-ci";
        };
      });

      devShells = forAllSystems (system:
        let
          pkgs = mkPkgs system;
        in
        {
          default = pkgs.mkShell {
            packages = [
              pkgs.mercury
              pkgs.gnumake
              pkgs.git
            ];

            shellHook = ''
              printf 'mercury=%s\n' "$(mmc --version | head -n 1)"
            '';
          };
        });
    };
}
