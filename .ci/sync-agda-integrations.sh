#!/usr/bin/env bash
set -euo pipefail

theorem="Exotic/FullCoupled/TheoremsMonolith.agda"

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

case "${1:-}" in
  --check)
    test -f "$theorem"
    test -n "${VEHICLE_AGDA_SOURCE:-}" || { echo "VEHICLE_AGDA_SOURCE is required"; exit 2; }
    test -f "$VEHICLE_AGDA_SOURCE/Vehicle.agda" || { echo "Vehicle.agda source is missing"; exit 1; }
    test -n "${SCHMITTY_AGDA_SOURCE:-}" || { echo "SCHMITTY_AGDA_SOURCE is required"; exit 2; }
    test -f "$SCHMITTY_AGDA_SOURCE/SMT/Backend/Z3.agda" || { echo "Schmitty Z3 backend is missing"; exit 1; }
    test -n "${AGDARSEC_AGDA_SOURCE:-}" || { echo "AGDARSEC_AGDA_SOURCE is required"; exit 2; }
    test -d "$AGDARSEC_AGDA_SOURCE" || { echo "agdarsec source is missing"; exit 1; }
    python3 - "$theorem" "$expected" <<'PY'
from pathlib import Path
import sys

path, expected = sys.argv[1], sys.argv[2]
text = Path(path).read_text(encoding="utf-8")
if expected.strip() not in text:
    raise SystemExit("scripted external Agda import block is stale")
print("agda-external-imports=pass")
PY
    ;;
  --write)
    python3 - "$theorem" "$expected" <<'PY'
from pathlib import Path
import sys

path, expected = sys.argv[1], sys.argv[2]
text = Path(path).read_text(encoding="utf-8")
begin = text.index("------------------------------------------------------------------------
-- BEGIN SCRIPTED EXTERNAL AGDA IMPORTS")
end_marker = "------------------------------------------------------------------------
-- END SCRIPTED EXTERNAL AGDA IMPORTS
------------------------------------------------------------------------"
end = text.index(end_marker, begin) + len(end_marker)
updated = text[:begin] + expected.rstrip() + text[end:]
Path(path).write_text(updated, encoding="utf-8")
print("scripted external Agda import block updated")
PY
    ;;
  *)
    echo "usage: $0 --check|--write" >&2
    exit 2
    ;;
esac
