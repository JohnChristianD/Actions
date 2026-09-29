{
  description = "Isolated Min, Gforth, and gbForth toolchain";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
  };

  outputs = { nixpkgs, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      forAllSystems = nixpkgs.lib.genAttrs systems;
    in
    {
      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs {
            inherit system;
          };

          minBootstrap = pkgs.writeShellScriptBin "ensure-min" ''
            set -euo pipefail

            root="''${MIN_LAB_HOME:-$PWD/.min-runtime}"
            home="$root/home"
            bin="$root/bin"

            mkdir -p "$home" "$bin"

            if [ ! -x "$bin/min" ]; then
              HOME="$home" ${pkgs.nimble}/bin/nimble install -y min
              installed="$home/.nimble/bin/min"

              test -x "$installed"
              ln -sf "$installed" "$bin/min"
            fi
          '';
        in
        {
          default = pkgs.mkShell {
            packages = [
              pkgs.gforth
              pkgs.gbforth
              pkgs.nim
              pkgs.nimble
              minBootstrap
            ];

            shellHook = ''
              export MIN_LAB_HOME="$PWD/.min-runtime"
              ensure-min
              export PATH="$MIN_LAB_HOME/bin:$PATH"
              echo "Min + Gforth + gbForth environment ready."
            '';
          };
        });
    };
}
