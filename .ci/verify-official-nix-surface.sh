#!/usr/bin/env bash
set -euo pipefail

for file in .github/workflows/*.yml .github/workflows/*.yaml; do
  [ -f "$file" ] || continue
  ! grep -Eq 'DeterminateSystems|cachix|nix-community|install-nix-action|install-nix\.sh|curl[[:space:]].*(nixos\.org/nix/install|artifacts\.nixos\.org/nix-installer)|nix-env([[:space:]]|$)|nix[[:space:]]+profile[[:space:]]+install' "$file" || {
    echo "unsupported third-party Nix installer/cache reference: $file"
    exit 1
  }
done

! grep -Eq 'doJailbreak|allowBroken[[:space:]]*=|allowUnsupportedSystem[[:space:]]*=' flake.nix || {
  echo "unsupported Nix override present in flake.nix"
  exit 1
}

! grep -Eq 'nixpkgs-ghc924|inversion-plugin-src|cau-placc/inversion-plugin' flake.nix || {
  echo "legacy compiler/plugin input present in flake.nix"
  exit 1
}

grep -Fq 'github:NixOS/nixpkgs/' flake.nix
grep -Fq 'github:agda/agda2hs/' flake.nix
grep -Fq 'github:martinescardo/TypeTopology/' flake.nix

inputs=$(awk '
  /^  inputs = \{/ { in_inputs=1; next }
  in_inputs && /^  \};/ { exit }
  in_inputs && /^[[:space:]]+[A-Za-z0-9_-]+[[:space:]]*=.*github:/ { print }
' flake.nix)

printf '%s\n' "$inputs" | grep -Eq '^    nixpkgs[[:space:]]*='
printf '%s\n' "$inputs" | grep -Eq '^    agda2hs[[:space:]]*='
printf '%s\n' "$inputs" | grep -Eq '^    typetopology[[:space:]]*='
! printf '%s\n' "$inputs" | grep -Eq 'nixpkgs-ghc924|inversion-plugin|DeterminateSystems|nix-community|cachix'

echo 'official-nix-surface=pass'
