#!/usr/bin/env bash
set -euo pipefail
canonical=FullCoupled/CanonicalLearnerMonolith.agda
theorem_graph=FullCoupled/TheoremsMonolith.agda
mode="${1:---check}"
block=$(mktemp)
tmp=$(mktemp)
trap 'rm -f "$block" "$tmp"' EXIT
sources() { git ls-files '*.agda' | LC_ALL=C sort; }
extract_block() { sed -n '/^-- BEGIN MIRTH-SYNC CANONICAL COMMAND$/,/^-- END MIRTH-SYNC CANONICAL COMMAND$/p' "$1"; }
extract_block "$canonical" > "$block"
[ -s "$block" ] || { echo 'canonical command block missing' >&2; exit 1; }
check_one() { file="$1"; extract_block "$file" | cmp -s "$block"; }
check_theorem_graph_command() {
  grep -Fqx -- "-- BEGIN MIRTH-SYNC THEOREM GRAPH COMMAND" "$theorem_graph" &&
  grep -Fqx -- "-- "$AGDA_COMMAND" --dependency-graph=.ci/discovery/theorems-monolith.dot -i . FullCoupled/TheoremsMonolith.agda" "$theorem_graph" &&
  grep -Fqx -- "-- END MIRTH-SYNC THEOREM GRAPH COMMAND" "$theorem_graph"
}
rewrite_one() {
  file="$1"
  if grep -Fq -- '-- BEGIN MIRTH-SYNC CANONICAL COMMAND' "$file"; then
    awk -v block="$block" '
      $0 == "-- BEGIN MIRTH-SYNC CANONICAL COMMAND" {
        while ((getline line < block) > 0) print line
        close(block); inside=1; next
      }
      $0 == "-- END MIRTH-SYNC CANONICAL COMMAND" { inside=0; next }
      !inside { print }
    ' "$file" > "$tmp"
  else
    awk -v block="$block" '
      /^module[[:space:]].*where[[:space:]]*$/ {
        print; print ""
        while ((getline line < block) > 0) print line
        close(block); print ""; next
      }
      { print }
    ' "$file" > "$tmp"
  fi
  mv "$tmp" "$file"
}
if [ "$mode" = "--check" ]; then
  failures=0
  while IFS= read -r file; do
    check_one "$file" || { echo "canonical command drift: $file" >&2; failures=$((failures + 1)); }
  done < <(sources)
  test "$failures" -eq 0
elif [ "$mode" = "--write" ]; then
  while IFS= read -r file; do rewrite_one "$file"; done < <(sources)
else
  echo 'usage: agda-command-sync [--check|--write]' >&2
  exit 2
fi
echo 'mirth-agda-command-sync=pass'
check_theorem_graph_command
echo "theorem-graph-command=$theorem_graph"
