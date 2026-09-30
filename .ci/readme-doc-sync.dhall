''
#!/usr/bin/env bash
set -euo pipefail

README=README.md
BEGIN='<!-- BEGIN GENERATED DOCUMENTATION INDEX -->'
END='<!-- END GENERATED DOCUMENTATION INDEX -->'
MODE=write
if [ "$#" -gt 0 ]; then
  MODE="$1"
fi

case "$MODE" in
  --check|--write) ;;
  *)
    echo "usage: readme-doc-sync [--check|--write]" >&2
    exit 2
    ;;
esac

tmp=$(mktemp)
trap 'rm -f "$tmp" "$README.tmp"' EXIT

git ls-files '*.md' '*.markdown' |
  while IFS= read -r path; do
    [ "$path" = "$README" ] && continue
    case "$path" in
      .ci/*) continue ;;
    esac
    [ -f "$path" ] || continue
    heading=$(sed -n 's/^# \(.*\)$/\1/p' "$path" | head -n 1)
    [ -n "$heading" ] || heading=$(basename "$path" | sed 's/\.[^.]*$//' | tr '-' ' ')
    printf '%s\t%s\n' "$path" "$heading"
  done | sort > "$tmp.docs"

count=$(wc -l < "$tmp.docs" | tr -d ' ')
{
  printf '%s\n\n' "$BEGIN"
  printf 'Generated from the tracked Markdown surface: %s files.\n' "$count"
  printf '%s\n\n' 'The root README is the GitHub-facing entry point; detailed evidence remains in the tracked source documents. Internal CI/discovery notes and historical agent plans are intentionally excluded from this public documentation index.'
  printf '%s\n\n' '### Repository documentation'
  while IFS="$(printf '\t')" read -r path title; do
    [ -n "$path" ] || continue
    printf '%s\n' "- \`$path\` — $title"
  done < "$tmp.docs"
  printf '\n%s\n' "$END"
} > "$tmp.generated"

start=$(grep -n -F -- "$BEGIN" "$README" | head -n 1 | cut -d: -f1)
finish=$(grep -n -F -- "$END" "$README" | head -n 1 | cut -d: -f1)
[ -n "$start" ] && [ -n "$finish" ] && [ "$start" -lt "$finish" ] || {
  echo "README generated documentation markers are missing" >&2
  exit 1
}

awk -v start="$start" -v finish="$finish" -v replacement="$tmp.generated" '
  NR == start {
    while ((getline line < replacement) > 0) print line
    in_block = 1
    next
  }
  in_block && NR == finish {
    in_block = 0
    next
  }
  !in_block { print }
' "$README" > "$README.tmp"
mv "$README.tmp" "$README"

if [ "$MODE" = "--check" ]; then
  git diff --exit-code -- "$README" >/dev/null || {
    echo "README documentation index is stale; run readme-doc-sync -- --write" >&2
    exit 1
  }
  echo "README documentation index synchronized."
else
  echo "README documentation index updated."
fi
PY
''
