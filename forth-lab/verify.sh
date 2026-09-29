#!/usr/bin/env bash
set -euo pipefail

root="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

cd "$root"

min examples/min/squares.min >"$tmp/min.out"
grep -F "Squares:" "$tmp/min.out"
grep -F "1" "$tmp/min.out"
grep -F "25" "$tmp/min.out"

gforth examples/gforth/hello.fs | grep -F "Hello from Gforth"

if [ "$(uname -s)" = "Linux" ] && [ "$(uname -m)" = "x86_64" ]; then
  factor examples/factor/hello.factor | grep -F "Hello from Factor"
else
  echo "Factor verification skipped: nixpkgs Factor package in this flake is x86_64-linux only."
fi

gbforth examples/gbforth/hello.fs "$tmp/hello.gb"
test -s "$tmp/hello.gb"

echo "All runnable lab checks passed."
