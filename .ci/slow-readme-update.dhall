in ''#!/usr/bin/env bash
set -euo pipefail

README=README.md
BEGIN='<!-- BEGIN RECENT COMMIT TOTALITY -->'
END='<!-- END RECENT COMMIT TOTALITY -->'
HEAD_SHA=$(git rev-parse HEAD)

last_processed=$(sed -n 's/^last-processed-commit: //p' "$README" | head -n 1)
if [ -z "$last_processed" ] || ! git cat-file -e "$last_processed^{commit}" 2>/dev/null; then
  echo "ERROR: README commit-totality marker is missing or invalid" >&2
  exit 1
fi

range="$last_processed..HEAD"
commits=$(git log --format='%H%x09%s' "$range")
count=$(printf '%s\n' "$commits" | sed '/^$/d' | wc -l | tr -d ' ')

if [ "$count" -eq 0 ]; then
  exit 0
fi

body=$(printf '%s\n' "$commits" | awk -F '\t' '{ print "- `" substr($1,1,12) "` " $2 }')

python3 - "$README" "$BEGIN" "$END" "$HEAD_SHA" "$count" "$body" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
begin, end, head, count, body = sys.argv[2:]
text = path.read_text()
start = text.index(begin)
finish = text.index(end, start) + len(end)
section = "\n".join([
    begin,
    f"last-processed-commit: {head}",
    f"unprocessed-commit-count: {count}",
    "",
    "The scheduled updater accounts for every commit since the previous processed commit.",
    "",
    body,
    end,
])
path.write_text(text[:start] + section + text[finish:])
PY
''
