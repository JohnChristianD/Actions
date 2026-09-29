{
  description = "Isolated Min, Gforth, gbForth, Factor, and Pony toolchain";

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
          ''';
        in
        {
          default = pkgs.mkShell {
            packages = [
              pkgs.gforth
              pkgs.gbforth
              pkgs.nim
              pkgs.nimble
              pkgs.ponyc
              minBootstrap
            ]
            ++ pkgs.lib.optionals (system == "x86_64-linux") [
              pkgs.factorPackages.factor-minimal
            ];

            shellHook = ''
              export MIN_LAB_HOME="$PWD/.min-runtime"
              ensure-min
              export PATH="$MIN_LAB_HOME/bin:$PATH"
              echo "Min + Gforth + gbForth + Pony environment ready."
              if [ "${system}" = "x86_64-linux" ]; then
                echo "Factor environment ready."
              fi
            ''';
          };
        });
    };
}
