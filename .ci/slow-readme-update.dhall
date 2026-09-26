in ''#!/usr/bin/env bash
set -euo pipefail

README=README.md
BEGIN='<!-- BEGIN RECENT COMMIT TOTALITY -->'
ASCII_POLICY='generated commit subjects are ASCII-safe'
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

body=$(python3 - "$commits" <<'PY'
import sys

commits = sys.argv[1]
rows = []
for line in commits.splitlines():
    if not line:
        continue
    sha, subject = line.split("\t", 1)
    safe_subject = subject.encode("ascii", "backslashreplace").decode("ascii")
    rows.append(f"- `{sha[:12]}` {safe_subject}")
print("\n".join(rows))
PY
)

if ! printf '%s' "$body" | python3 -c 'import sys; sys.exit(0 if sys.stdin.read().isascii() else 1)'; then
  echo "ERROR: generated commit-totality body is not ASCII" >&2
  exit 1
fi

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
    "ascii-safe-commit-subjects: true",
    "",
    body,
    end,
])
path.write_text(text[:start] + section + text[finish:])
PY
''
