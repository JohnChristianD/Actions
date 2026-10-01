''
#!/usr/bin/env bash
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

if printf '%s\n' "$commits" | LC_ALL=C grep -q '[^[:print:][:space:]]'; then
  echo "ERROR: commit subjects are not ASCII-safe" >&2
  exit 1
fi

body=$(printf '%s\n' "$commits" | awk -F '\t' 'NF >= 2 { printf "- \`%s\` %s\n", substr($1,1,12), $2 }')

tmp=$(mktemp)
trap 'rm -f "$tmp" "$README.tmp"' EXIT
awk -v begin="$BEGIN" -v end="$END" -v head="$HEAD_SHA" -v count="$count" -v body="$body" '
  $0 == begin && !replaced {
    print begin
    print "last-processed-commit: " head
    print "unprocessed-commit-count: " count
    print ""
    print "The scheduled updater accounts for every commit since the previous processed commit."
    print "ascii-safe-commit-subjects: true"
    print ""
    print body
    print end
    in_block = 1
    replaced = 1
    next
  }
  in_block && $0 == end { in_block = 0; next }
  !in_block { print }
' "$README" > "$README.tmp"
mv "$README.tmp" "$README"
''
