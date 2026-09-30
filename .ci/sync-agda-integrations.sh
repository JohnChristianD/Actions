#!/usr/bin/env bash
set -euo pipefail

theorem="FullCoupled/TheoremsMonolith.agda"

expected='
------------------------------------------------------------------------
-- BEGIN SCRIPTED EXTERNAL AGDA IMPORTS
-- Synced by .ci/sync-agda-integrations.sh; keep this block in the
-- theorem monolith and do not materialize a third Agda source file.
------------------------------------------------------------------------

import SMT.Theories.Ints as Ints
open import SMT.Backend.Z3 Ints.theory
import Vehicle

------------------------------------------------------------------------
-- END SCRIPTED EXTERNAL AGDA IMPORTS
------------------------------------------------------------------------
'

extract() {
  awk '
    /^------------------------------------------------------------------------$/ && getline line {
      if (line == "-- BEGIN SCRIPTED EXTERNAL AGDA IMPORTS") {
        print "------------------------------------------------------------------------"
        print line
        while ((getline line) > 0) {
          print line
          if (line == "-- END SCRIPTED EXTERNAL AGDA IMPORTS") {
            getline line
            print line
            exit
          }
        }
        exit 1
      }
    }
  ' "$1"
}

case "${1:-}" in
  --check)
    test -f "$theorem"
    test -n "${VEHICLE_AGDA_SOURCE:-}" || { echo "VEHICLE_AGDA_SOURCE is required"; exit 2; }
    test -f "$VEHICLE_AGDA_SOURCE/Vehicle.agda" || { echo "Vehicle.agda source is missing"; exit 1; }
    test -n "${SCHMITTY_AGDA_SOURCE:-}" || { echo "SCHMITTY_AGDA_SOURCE is required"; exit 2; }
    test -f "$SCHMITTY_AGDA_SOURCE/SMT/Backend/Z3.agda" || { echo "Schmitty Z3 backend is missing"; exit 1; }
    test -n "${AGDARSEC_AGDA_SOURCE:-}" || { echo "AGDARSEC_AGDA_SOURCE is required"; exit 2; }
    test -d "$AGDARSEC_AGDA_SOURCE" || { echo "agdarsec source is missing"; exit 1; }
    actual=$(extract "$theorem")
    test "$actual" = "${expected#$'\\n'}" || {
      printf '%s\n' "$actual"
      echo "scripted external Agda import block is stale" >&2
      exit 1
    }
    echo "agda-external-imports=pass"
    ;;
  --write)
    tmp=$(mktemp)
    trap 'rm -f "$tmp" "$theorem.tmp"' EXIT
    printf '%s\n' "$expected" > "$tmp"
    awk -v replacement="$tmp" '
      /^------------------------------------------------------------------------$/ && !inside && getline line {
        if (line == "-- BEGIN SCRIPTED EXTERNAL AGDA IMPORTS") {
          while ((getline repl < replacement) > 0) print repl
          while ((getline line) > 0) {
            if (line == "-- END SCRIPTED EXTERNAL AGDA IMPORTS") {
              getline line
              break
            }
          }
          while ((getline line) > 0) print line
          next
        }
      }
      { print }
    ' "$theorem" > "$theorem.tmp"
    mv "$theorem.tmp" "$theorem"
    echo "scripted external Agda import block updated"
    ;;
  *)
    echo "usage: $0 --check|--write" >&2
    exit 2
    ;;
esac
