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
              pkgs.gh
              pkgs.python3
            ];
            shellHook = ''
              export PATH="\${pkgs.mercury}/bin:$PATH"
            '';
          };
        });
    };
}
