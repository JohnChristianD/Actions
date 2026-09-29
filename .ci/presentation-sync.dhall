''
#!/usr/bin/env bash
set -euo pipefail

tmp="${RUNNER_TEMP:-/tmp}/actions-presentation-sync"
rm -rf "$tmp"
mkdir -p "$tmp"

(cd .ci/discovery && mmc --make theorem_surface_sync && ./theorem_surface_sync)

dhall type --file .ci/discovery/theorem-surface.dhall >/dev/null
dhall-to-json --file .ci/discovery/theorem-surface.dhall > "$tmp/theorem-surface.json"

python3 - "$tmp/theorem-surface.json" "$tmp/src" <<'PY'
from pathlib import Path
import json
import sys

report_path = Path(sys.argv[1])
src = Path(sys.argv[2])
report = json.loads(report_path.read_text(encoding="utf-8"))
names = report["semanticLawNames"]
if not names:
    raise SystemExit("theorem surface is empty")

def elm_string(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\\"') + '"'

src.mkdir(parents=True, exist_ok=True)
generated = """module GeneratedTheoremSurface exposing (semanticLawCount, semanticLawNames)

semanticLawCount : Int
semanticLawCount =
    %d

semanticLawNames : List String
semanticLawNames =
    [ %s ]
""" % (report["semanticLawCount"], ", ".join(elm_string(name) for name in names))

(src / "GeneratedTheoremSurface.elm").write_text(generated, encoding="utf-8")
PY
''
