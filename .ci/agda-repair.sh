#!/usr/bin/env bash
set -euo pipefail

usage() {
  printf 'usage: %s normalize SOURCE\n' "$0" >&2
  printf '       %s repair SOURCE ERROR_LOG\n' "$0" >&2
  exit 2
}

normalize() {
  local source=$1
  local tmp
  tmp=$(mktemp)
  trap 'rm -f "$tmp"' RETURN
  tr -d '\r' < "$source" \
    | sed -e 's/[[:space:]]*$//' \
          -e '${/^$/d;}' > "$tmp"
  printf '\n' >> "$tmp"
  if ! cmp -s "$source" "$tmp"; then
    cat "$tmp" > "$source"
  fi
}

repair() {
  local source=$1
  local error_log=$2

  normalize "$source"

  case "$(grep -oE 'Not in scope: [A-Za-z0-9_]+' "$error_log" | head -n 1 || true)" in
    'Not in scope: suc')
      if grep -Fq 'open import Agda.Builtin.Nat using (Nat; zero; suc)' "$source"; then
        return 0
      fi
      sed -i '/^module .* where$/a open import Agda.Builtin.Nat using (Nat; zero; suc)' "$source"
      ;;
    *)
      printf 'No allowlisted Agda repair applies.\n' >&2
      return 1
      ;;
  esac
}

case "${1:-}" in
  normalize)
    [ "$#" -eq 2 ] || usage
    normalize "$2"
    ;;
  repair)
    [ "$#" -eq 3 ] || usage
    repair "$2" "$3"
    ;;
  *)
    usage
    ;;
esac
